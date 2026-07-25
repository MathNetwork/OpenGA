import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.AbstractChartPullCutoff
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.ChartTransition.TensorChartTransition
import DifferentialGeometry.Analysis.Sobolev.Chart.CrossChartBounds.CrossChartBoundStrict

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean

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

private lemma ae_eq_of_ae_eq_restrict_of_eqOn_compl
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f h : X → ℝ} {s : Set X} (hs : MeasurableSet s)
    (h_restrict : f =ᵐ[μ.restrict s] h)
    (h_compl : ∀ x, x ∉ s → f x = h x) :
    f =ᵐ[μ] h := by
  rw [Filter.EventuallyEq, MeasureTheory.ae_iff]
  have h_diff_subset : {x | ¬ f x = h x} ⊆ s := by
    intro x hx
    by_contra hxs
    exact hx (h_compl x hxs)
  have h_inter : {x | ¬ f x = h x} = {x | ¬ f x = h x} ∩ s :=
    (Set.inter_eq_left.mpr h_diff_subset).symm
  rw [Filter.EventuallyEq, MeasureTheory.ae_iff] at h_restrict
  rw [MeasureTheory.Measure.restrict_apply₀'] at h_restrict
  · rwa [h_inter]
  · exact hs.nullMeasurableSet


def transportCoeffManifold
    (_g : SmoothRiemannianMetric I M) (r s : ℕ) (β α : M)
    (P₀ Q : TensorCompIdx (E := E) r s) : M → ℝ :=
  fun x =>
    ((chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x *
      ((chartKernelCutoff (I := I) (M := M) β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x *
        transitionCoeff (E := E) (I := I) (M := M) r s β α P₀ Q x

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
@[simp] lemma transportCoeffManifold_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (β α : M)
    (P₀ Q : TensorCompIdx (E := E) r s) (x : M) :
    transportCoeffManifold (I := I) (M := M) g r s β α P₀ Q x =
      ((chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x *
        ((chartKernelCutoff (I := I) (M := M) β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x *
          transitionCoeff (E := E) (I := I) (M := M) r s β α P₀ Q x := rfl

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma transportCoeffManifold_eq_zero_of_cutoffα_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (β α : M)
    (P₀ Q : TensorCompIdx (E := E) r s) {x : M}
    (hx : ((chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x = 0) :
    transportCoeffManifold (I := I) (M := M) g r s β α P₀ Q x = 0 := by
  rw [transportCoeffManifold_apply, hx]; ring

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma transportCoeffManifold_eq_zero_of_cutoffβ_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (β α : M)
    (P₀ Q : TensorCompIdx (E := E) r s) {x : M}
    (hx : ((chartKernelCutoff (I := I) (M := M) β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x = 0) :
    transportCoeffManifold (I := I) (M := M) g r s β α P₀ Q x = 0 := by
  rw [transportCoeffManifold_apply, hx]; ring

private def transportSupportSet (α β : M) : Set M :=
  tsupport ((chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯) : M → ℝ) ∩
    tsupport ((chartKernelCutoff (I := I) (M := M) β : C^∞⟮I, M; ℝ⟯) : M → ℝ)

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma transportSupportSet_isCompact (α β : M) :
    IsCompact (transportSupportSet (I := I) (M := M) α β) :=
  (chartKernelCutoff_hasCompactSupport (I := I) (M := M) α).inter_right
    (isClosed_tsupport _)

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma transportSupportSet_isClosed (α β : M) :
    IsClosed (transportSupportSet (I := I) (M := M) α β) :=
  (isClosed_tsupport _).inter (isClosed_tsupport _)

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma transportSupportSet_subset_sourceα (α β : M) :
    transportSupportSet (I := I) (M := M) α β ⊆ (chartAt H α).source :=
  fun _ hx => chartKernelCutoff_tsupport_subset_source (I := I) (M := M) α hx.1

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma transportSupportSet_subset_sourceβ (α β : M) :
    transportSupportSet (I := I) (M := M) α β ⊆ (chartAt H β).source :=
  fun _ hx => chartKernelCutoff_tsupport_subset_source (I := I) (M := M) β hx.2

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma tsupport_transportCoeffManifold_subset
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (β α : M)
    (P₀ Q : TensorCompIdx (E := E) r s) :
    tsupport (transportCoeffManifold (I := I) (M := M) g r s β α P₀ Q) ⊆
      transportSupportSet (I := I) (M := M) α β := by
  refine closure_minimal ?_ (transportSupportSet_isClosed (I := I) (M := M) α β)
  intro x hx
  rw [Function.mem_support] at hx
  refine ⟨?_, ?_⟩
  · by_contra hxα
    exact hx (transportCoeffManifold_eq_zero_of_cutoffα_zero
      (I := I) (M := M) g r s β α P₀ Q
      (image_eq_zero_of_notMem_tsupport hxα))
  · by_contra hxβ
    exact hx (transportCoeffManifold_eq_zero_of_cutoffβ_zero
      (I := I) (M := M) g r s β α P₀ Q
      (image_eq_zero_of_notMem_tsupport hxβ))

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem hasCompactSupport_transportCoeffManifold
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (β α : M)
    (P₀ Q : TensorCompIdx (E := E) r s) :
    HasCompactSupport (transportCoeffManifold (I := I) (M := M) g r s β α P₀ Q) :=
  HasCompactSupport.of_support_subset_isCompact
    (transportSupportSet_isCompact (I := I) (M := M) α β)
    (fun _ hx => tsupport_transportCoeffManifold_subset
      (I := I) (M := M) g r s β α P₀ Q (subset_tsupport _ hx))

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma tsupport_transportCoeffManifold_subset_sourceα
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (β α : M)
    (P₀ Q : TensorCompIdx (E := E) r s) :
    tsupport (transportCoeffManifold (I := I) (M := M) g r s β α P₀ Q) ⊆
      (chartAt H α).source :=
  (tsupport_transportCoeffManifold_subset (I := I) (M := M) g r s β α P₀ Q).trans
    (transportSupportSet_subset_sourceα (I := I) (M := M) α β)

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma tsupport_transportCoeffManifold_subset_sourceβ
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (β α : M)
    (P₀ Q : TensorCompIdx (E := E) r s) :
    tsupport (transportCoeffManifold (I := I) (M := M) g r s β α P₀ Q) ⊆
      (chartAt H β).source :=
  (tsupport_transportCoeffManifold_subset (I := I) (M := M) g r s β α P₀ Q).trans
    (transportSupportSet_subset_sourceβ (I := I) (M := M) α β)

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem contMDiff_transportCoeffManifold
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (β α : M)
    (P₀ Q : TensorCompIdx (E := E) r s) :
    ContMDiff I (𝓘(ℝ, ℝ)) ∞
      (transportCoeffManifold (I := I) (M := M) g r s β α P₀ Q) := by
  classical
  intro x
  by_cases hx_overlap : x ∈ (chartAt H β).source ∩ (chartAt H α).source
  · have hcutα : ContMDiffAt I (𝓘(ℝ, ℝ)) ∞
        (fun y : M => ((chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯) :
          M → ℝ) y) x :=
      ((chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯).contMDiff).contMDiffAt
    have hcutβ : ContMDiffAt I (𝓘(ℝ, ℝ)) ∞
        (fun y : M => ((chartKernelCutoff (I := I) (M := M) β : C^∞⟮I, M; ℝ⟯) :
          M → ℝ) y) x :=
      ((chartKernelCutoff (I := I) (M := M) β : C^∞⟮I, M; ℝ⟯).contMDiff).contMDiffAt
    have h_overlap_open : IsOpen
        ((chartAt H β).source ∩ (chartAt H α).source) :=
      (chartAt H β).open_source.inter (chartAt H α).open_source
    have hcoeff_on :=
      contMDiffOn_transitionCoeff (E := E) (I := I) (M := M) r s β α P₀ Q
    have hcoeff_at : ContMDiffAt I (𝓘(ℝ, ℝ)) ∞
        (transitionCoeff (E := E) (I := I) (M := M) r s β α P₀ Q) x :=
      hcoeff_on.contMDiffAt (h_overlap_open.mem_nhds hx_overlap)
    have hprod : ContMDiffAt I (𝓘(ℝ, ℝ)) ∞
        (transportCoeffManifold (I := I) (M := M) g r s β α P₀ Q) x := by
      have := (hcutα.mul hcutβ).mul hcoeff_at
      simpa [transportCoeffManifold] using this
    exact hprod
  · have hsupp_sub := tsupport_transportCoeffManifold_subset
      (I := I) (M := M) g r s β α P₀ Q
    have hx_notin : x ∉ tsupport (transportCoeffManifold
        (I := I) (M := M) g r s β α P₀ Q) := by
      intro hxsupp
      have hxss := hsupp_sub hxsupp
      exact hx_overlap ⟨transportSupportSet_subset_sourceβ
        (I := I) (M := M) α β hxss,
        transportSupportSet_subset_sourceα (I := I) (M := M) α β hxss⟩
    refine ContMDiffAt.congr_of_eventuallyEq
      (f := fun _ : M => (0 : ℝ)) contMDiffAt_const ?_
    have hopen : IsOpen (tsupport (transportCoeffManifold
        (I := I) (M := M) g r s β α P₀ Q))ᶜ :=
      (isClosed_tsupport _).isOpen_compl
    filter_upwards [hopen.mem_nhds hx_notin] with y hy
    have hy_notin : y ∉ Function.support (transportCoeffManifold
        (I := I) (M := M) g r s β α P₀ Q) := fun h => hy (subset_tsupport _ h)
    by_contra hne
    exact hy_notin hne

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma continuous_transportCoeffManifold
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (β α : M)
    (P₀ Q : TensorCompIdx (E := E) r s) :
    Continuous (transportCoeffManifold (I := I) (M := M) g r s β α P₀ Q) :=
  (contMDiff_transportCoeffManifold (I := I) (M := M) g r s β α P₀ Q).continuous

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem exists_bound_transportCoeffManifold
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (β α : M)
    (P₀ Q : TensorCompIdx (E := E) r s) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x, |transportCoeffManifold (I := I) (M := M) g r s β α P₀ Q x| ≤ C := by
  obtain ⟨C, hC⟩ :=
    (hasCompactSupport_transportCoeffManifold (I := I) (M := M) g r s β α P₀ Q).exists_bound_of_continuous
      (continuous_transportCoeffManifold (I := I) (M := M) g r s β α P₀ Q)
  refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
  have hx := hC x
  rw [Real.norm_eq_abs] at hx
  exact hx.trans (le_max_left _ _)

private def transportCoeffPushed
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (β α : M)
    (P₀ Q : TensorCompIdx (E := E) r s) : EuclN → ℝ :=
  chartPushedRaw (I := I) (M := M) α
    (transportCoeffManifold (I := I) (M := M) g r s β α P₀ Q)

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma exists_bound_transportCoeffPushed
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (β α : M)
    (P₀ Q : TensorCompIdx (E := E) r s) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ y, |transportCoeffPushed (I := I) (M := M) g r s β α P₀ Q y| ≤ C := by
  obtain ⟨C, hC_nn, hC⟩ :=
    exists_bound_transportCoeffManifold (I := I) (M := M) g r s β α P₀ Q
  refine ⟨C, hC_nn, fun y => ?_⟩
  unfold transportCoeffPushed
  by_cases hy : y ∈ chartTargetEuclid (I := I) (M := M) α
  · rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy]
    exact hC _
  · rw [chartPushedRaw_apply_of_notMem (I := I) (M := M) α _ hy, abs_zero]
    exact hC_nn

private structure TransportDiffeoData
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (β α : M)
    (P₀ Q : TensorCompIdx (E := E) r s) where
  Ωαβ : Set EuclN
  Ωβα : Set EuclN
  hΩαβ_open : IsOpen Ωαβ
  hΩαβ_subset_target : Ωαβ ⊆ chartTargetEuclid (I := I) (M := M) α
  hΩβα_subset_target : Ωβα ⊆ chartTargetEuclid (I := I) (M := M) β
  Φ : SmoothDiffeoBoundedAtOrder (Module.finrank ℝ E) Ωαβ Ωβα 0
  hΦ_eq : ∀ y ∈ Ωαβ, Φ.toFun y = chartTransitionEuclid (I := I) (M := M) α β y
  hsupp_subset : ∀ y, transportCoeffPushed (I := I) (M := M) g r s β α P₀ Q y ≠ 0 →
    y ∈ Ωαβ

omit [CompleteSpace E] in
private lemma exists_transportDiffeoData
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (β α : M)
    (P₀ Q : TensorCompIdx (E := E) r s) :
    Nonempty (TransportDiffeoData (I := I) (M := M) g r s β α P₀ Q) := by
  classical
  obtain ⟨Ωαβ, Ωβα, hΩαβ_open, _hΩβα_open, hΩαβ_subset_target,
    hΩβα_subset_target, _hΩαβ_overlap, _hΩβα_overlap, h_image_subset, Φ,
    hΦ_eq, _hΦ_inv_eq⟩ :=
    chartTransition_smoothDiffeoBoundedAtOrder_strict (I := I) (M := M)
      α β
      (transportSupportSet_isCompact (I := I) (M := M) α β)
      (transportSupportSet_subset_sourceα (I := I) (M := M) α β)
      (transportSupportSet_subset_sourceβ (I := I) (M := M) α β)
      0
  refine ⟨{
    Ωαβ := Ωαβ
    Ωβα := Ωβα
    hΩαβ_open := hΩαβ_open
    hΩαβ_subset_target := hΩαβ_subset_target
    hΩβα_subset_target := hΩβα_subset_target
    Φ := Φ
    hΦ_eq := hΦ_eq
    hsupp_subset := ?_ }⟩
  intro y hy
  by_cases hy_target : y ∈ chartTargetEuclid (I := I) (M := M) α
  · set z : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hz_def
    have hsymm_target : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
      rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy_target
      exact hy_target
    have hcoeff_ne : transportCoeffManifold (I := I) (M := M) g r s β α P₀ Q z ≠ 0 := by
      intro h0
      apply hy
      unfold transportCoeffPushed
      rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy_target, ← hz_def, h0]
    have hz_supp : z ∈ transportSupportSet (I := I) (M := M) α β :=
      tsupport_transportCoeffManifold_subset (I := I) (M := M) g r s β α P₀ Q
        (subset_tsupport _ (Function.mem_support.mpr hcoeff_ne))
    have hy_eq_image : (toEuclidean (E := E)) (extChartAt I α z) = y := by
      rw [hz_def, (extChartAt I α).right_inv hsymm_target]
      exact (toEuclidean (E := E)).apply_symm_apply y
    have hy_in_image :
        y ∈ ((toEuclidean : E ≃L[ℝ] _) ∘ extChartAt I α) ''
          (transportSupportSet (I := I) (M := M) α β) :=
      ⟨z, hz_supp, hy_eq_image⟩
    exact h_image_subset hy_in_image
  · exact absurd
      (by unfold transportCoeffPushed
          exact chartPushedRaw_apply_of_notMem (I := I) (M := M) α _ hy_target) hy

private def transportFun
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (β α : M)
    (P₀ Q : TensorCompIdx (E := E) r s)
    (f : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ :=
  fun y => transportCoeffPushed (I := I) (M := M) g r s β α P₀ Q y *
    (f : EuclN → ℝ) (chartTransitionEuclid (I := I) (M := M) α β y)

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma transportFun_eq_comp_Φ
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (β α : M)
    (P₀ Q : TensorCompIdx (E := E) r s)
    (D : TransportDiffeoData (I := I) (M := M) g r s β α P₀ Q)
    (f : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
    transportFun (I := I) (M := M) g r s β α P₀ Q f =
      fun y => transportCoeffPushed (I := I) (M := M) g r s β α P₀ Q y *
        (f : EuclN → ℝ) (D.Φ.toFun y) := by
  funext y
  unfold transportFun
  by_cases hy : transportCoeffPushed (I := I) (M := M) g r s β α P₀ Q y = 0
  · rw [hy, zero_mul, zero_mul]
  · rw [D.hΦ_eq y (D.hsupp_subset y hy)]

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma transportFun_eq_zero_off_Ωαβ
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (β α : M)
    (P₀ Q : TensorCompIdx (E := E) r s)
    (D : TransportDiffeoData (I := I) (M := M) g r s β α P₀ Q)
    (f : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) {y : EuclN}
    (hy : y ∉ D.Ωαβ) :
    transportFun (I := I) (M := M) g r s β α P₀ Q f y = 0 := by
  unfold transportFun
  have hcoeff : transportCoeffPushed (I := I) (M := M) g r s β α P₀ Q y = 0 := by
    by_contra hne
    exact hy (D.hsupp_subset y hne)
  rw [hcoeff, zero_mul]

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma transportFun_eq_indicator
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (β α : M)
    (P₀ Q : TensorCompIdx (E := E) r s)
    (D : TransportDiffeoData (I := I) (M := M) g r s β α P₀ Q)
    (f : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
    transportFun (I := I) (M := M) g r s β α P₀ Q f =
      D.Ωαβ.indicator (fun y => transportCoeffPushed
        (I := I) (M := M) g r s β α P₀ Q y * (f : EuclN → ℝ) (D.Φ.toFun y)) := by
  funext y
  by_cases hy : y ∈ D.Ωαβ
  · rw [Set.indicator_of_mem hy,
      transportFun_eq_comp_Φ (I := I) (M := M) g r s β α P₀ Q D f]
  · rw [Set.indicator_of_notMem hy,
      transportFun_eq_zero_off_Ωαβ (I := I) (M := M) g r s β α P₀ Q D f hy]

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma chartL2Measure_restrict_Ωαβ
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (β α : M)
    (P₀ Q : TensorCompIdx (E := E) r s)
    (D : TransportDiffeoData (I := I) (M := M) g r s β α P₀ Q) :
    (chartL2Measure (I := I) (M := M) α).restrict D.Ωαβ =
      (volume : Measure EuclN).restrict D.Ωαβ := by
  rw [chartL2Measure, Measure.restrict_restrict_of_subset D.hΩαβ_subset_target]

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma Ωαβ_measurableSet
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (β α : M)
    (P₀ Q : TensorCompIdx (E := E) r s)
    (D : TransportDiffeoData (I := I) (M := M) g r s β α P₀ Q) :
    MeasurableSet D.Ωαβ :=
  D.hΩαβ_open.measurableSet

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
private lemma aestronglyMeasurable_transportCoeffPushed
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (β α : M)
    (P₀ Q : TensorCompIdx (E := E) r s) :
    AEStronglyMeasurable
      (transportCoeffPushed (I := I) (M := M) g r s β α P₀ Q)
      (chartL2Measure (I := I) (M := M) α) := by
  classical
  unfold transportCoeffPushed chartL2Measure
  refine ContinuousOn.aestronglyMeasurable ?_
    (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) α).measurableSet
  have h_inner : ContinuousOn
      (fun y : EuclN => (transportCoeffManifold
        (I := I) (M := M) g r s β α P₀ Q)
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))
      (chartTargetEuclid (I := I) (M := M) α) := by
    refine (continuous_transportCoeffManifold
      (I := I) (M := M) g r s β α P₀ Q).comp_continuousOn ?_
    refine (continuousOn_extChartAt_symm α).comp
      (toEuclidean (E := E)).symm.continuous.continuousOn ?_
    intro y hy
    rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
    exact hy
  refine h_inner.congr ?_
  intro y hy
  exact chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
private lemma aestronglyMeasurable_transportFun
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (β α : M)
    (P₀ Q : TensorCompIdx (E := E) r s)
    (D : TransportDiffeoData (I := I) (M := M) g r s β α P₀ Q)
    (f : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
    AEStronglyMeasurable (transportFun (I := I) (M := M) g r s β α P₀ Q f)
      (chartL2Measure (I := I) (M := M) α) := by
  classical
  rw [transportFun_eq_indicator (I := I) (M := M) g r s β α P₀ Q D f]
  rw [aestronglyMeasurable_indicator_iff
    (Ωαβ_measurableSet (I := I) (M := M) g r s β α P₀ Q D),
    chartL2Measure_restrict_Ωαβ (I := I) (M := M) g r s β α P₀ Q D]
  have h_coeff : AEStronglyMeasurable
      (transportCoeffPushed (I := I) (M := M) g r s β α P₀ Q)
      ((volume : Measure EuclN).restrict D.Ωαβ) := by
    have h := aestronglyMeasurable_transportCoeffPushed
      (I := I) (M := M) g r s β α P₀ Q
    rw [← chartL2Measure_restrict_Ωαβ (I := I) (M := M) g r s β α P₀ Q D]
    exact h.restrict
  have h_f_meas : AEStronglyMeasurable (f : EuclN → ℝ)
      ((volume : Measure EuclN).restrict D.Ωβα) :=
    (Lp.aestronglyMeasurable f).mono_measure
      (by rw [chartL2Measure]
          exact Measure.restrict_mono D.hΩβα_subset_target le_rfl)
  have h_comp : AEStronglyMeasurable (fun y => (f : EuclN → ℝ) (D.Φ.toFun y))
      ((volume : Measure EuclN).restrict D.Ωαβ) :=
    h_f_meas.comp_quasiMeasurePreserving D.Φ.toFun_quasiMeasurePreserving
  exact h_coeff.mul h_comp

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma exists_eLpNorm_transportFun_bound
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (β α : M)
    (P₀ Q : TensorCompIdx (E := E) r s)
    (D : TransportDiffeoData (I := I) (M := M) g r s β α P₀ Q) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ f : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β),
        eLpNorm (transportFun (I := I) (M := M) g r s β α P₀ Q f) 2
            (chartL2Measure (I := I) (M := M) α) ≤
          ENNReal.ofReal K * eLpNorm (f : EuclN → ℝ) 2
            (chartL2Measure (I := I) (M := M) β) := by
  classical
  obtain ⟨C, hC_nn, hC⟩ :=
    exists_bound_transportCoeffPushed (I := I) (M := M) g r s β α P₀ Q
  set Kchg : ℝ := (1 / D.Φ.jacobian_lower_bound) ^ (1 / (2 : ℝ≥0∞).toReal)
    with hKchg_def
  have hjLB_pos : 0 < D.Φ.jacobian_lower_bound := D.Φ.jacobian_lower_bound_pos
  have hKchg_nn : 0 ≤ Kchg := by
    rw [hKchg_def]
    have h_inv_nn : (0 : ℝ) ≤ 1 / D.Φ.jacobian_lower_bound := by positivity
    exact Real.rpow_nonneg h_inv_nn _
  refine ⟨C * Kchg, mul_nonneg hC_nn hKchg_nn, fun f => ?_⟩
  have h_pointwise : ∀ y, ‖transportFun (I := I) (M := M) g r s β α P₀ Q f y‖ ≤
      ‖(C • D.Ωαβ.indicator (fun y => (f : EuclN → ℝ) (D.Φ.toFun y))) y‖ := by
    intro y
    rw [transportFun_eq_indicator (I := I) (M := M) g r s β α P₀ Q D f]
    by_cases hy : y ∈ D.Ωαβ
    · rw [Set.indicator_of_mem hy, Pi.smul_apply, Set.indicator_of_mem hy,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, smul_eq_mul, abs_mul]
      refine mul_le_mul_of_nonneg_right ((hC _).trans ?_) (abs_nonneg _)
      exact le_abs_self C
    · rw [Set.indicator_of_notMem hy, norm_zero]
      positivity
  have h_step1 : eLpNorm (transportFun (I := I) (M := M) g r s β α P₀ Q f) 2
      (chartL2Measure (I := I) (M := M) α) ≤
        ENNReal.ofReal C *
          eLpNorm (D.Ωαβ.indicator (fun y => (f : EuclN → ℝ) (D.Φ.toFun y))) 2
            (chartL2Measure (I := I) (M := M) α) := by
    refine (eLpNorm_mono_ae (Filter.Eventually.of_forall h_pointwise)).trans ?_
    rw [show (C • D.Ωαβ.indicator (fun y => (f : EuclN → ℝ) (D.Φ.toFun y))) =
        (C : ℝ) • D.Ωαβ.indicator (fun y => (f : EuclN → ℝ) (D.Φ.toFun y)) from rfl]
    refine (eLpNorm_const_smul_le).trans ?_
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg hC_nn]
  have h_indic : eLpNorm
      (D.Ωαβ.indicator (fun y => (f : EuclN → ℝ) (D.Φ.toFun y))) 2
        (chartL2Measure (I := I) (M := M) α) =
      eLpNorm (fun y => (f : EuclN → ℝ) (D.Φ.toFun y)) 2
        ((volume : Measure EuclN).restrict D.Ωαβ) := by
    rw [eLpNorm_indicator_eq_eLpNorm_restrict
      (Ωαβ_measurableSet (I := I) (M := M) g r s β α P₀ Q D),
      chartL2Measure_restrict_Ωαβ (I := I) (M := M) g r s β α P₀ Q D]
  have h_chg : eLpNorm (fun y => (f : EuclN → ℝ) (D.Φ.toFun y)) 2
      ((volume : Measure EuclN).restrict D.Ωαβ) ≤
        ENNReal.ofReal Kchg *
          eLpNorm (f : EuclN → ℝ) 2 ((volume : Measure EuclN).restrict D.Ωβα) := by
    rw [hKchg_def]
    exact D.Φ.eLpNorm_comp_toFun_le_const (by norm_num) (by norm_num)
      D.hΩαβ_open (f : EuclN → ℝ)
  have h_mono : eLpNorm (f : EuclN → ℝ) 2
      ((volume : Measure EuclN).restrict D.Ωβα) ≤
        eLpNorm (f : EuclN → ℝ) 2 (chartL2Measure (I := I) (M := M) β) := by
    have h_le : (volume : Measure EuclN).restrict D.Ωβα ≤
        chartL2Measure (I := I) (M := M) β :=
      Measure.restrict_mono D.hΩβα_subset_target le_rfl
    exact eLpNorm_mono_measure _ h_le
  calc eLpNorm (transportFun (I := I) (M := M) g r s β α P₀ Q f) 2
        (chartL2Measure (I := I) (M := M) α)
      ≤ ENNReal.ofReal C *
          eLpNorm (D.Ωαβ.indicator (fun y => (f : EuclN → ℝ) (D.Φ.toFun y))) 2
            (chartL2Measure (I := I) (M := M) α) := h_step1
    _ = ENNReal.ofReal C * eLpNorm (fun y => (f : EuclN → ℝ) (D.Φ.toFun y)) 2
            ((volume : Measure EuclN).restrict D.Ωαβ) := by rw [h_indic]
    _ ≤ ENNReal.ofReal C * (ENNReal.ofReal Kchg *
            eLpNorm (f : EuclN → ℝ) 2
              ((volume : Measure EuclN).restrict D.Ωβα)) :=
          mul_le_mul_of_nonneg_left h_chg (zero_le _)
    _ ≤ ENNReal.ofReal C * (ENNReal.ofReal Kchg *
            eLpNorm (f : EuclN → ℝ) 2 (chartL2Measure (I := I) (M := M) β)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left h_mono (zero_le _)) (zero_le _)
    _ = ENNReal.ofReal (C * Kchg) *
            eLpNorm (f : EuclN → ℝ) 2 (chartL2Measure (I := I) (M := M) β) := by
          rw [ENNReal.ofReal_mul hC_nn, mul_assoc]

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
private lemma memLp_transportFun
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (β α : M)
    (P₀ Q : TensorCompIdx (E := E) r s)
    (D : TransportDiffeoData (I := I) (M := M) g r s β α P₀ Q)
    (f : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
    MemLp (transportFun (I := I) (M := M) g r s β α P₀ Q f) 2
      (chartL2Measure (I := I) (M := M) α) := by
  refine ⟨aestronglyMeasurable_transportFun (I := I) (M := M) g r s β α P₀ Q D f,
    ?_⟩
  obtain ⟨K, hK_nn, hK⟩ :=
    exists_eLpNorm_transportFun_bound (I := I) (M := M) g r s β α P₀ Q D
  refine lt_of_le_of_lt (hK f) ?_
  refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
  exact (Lp.memLp f).2

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma transportFun_aux_ae_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (β α : M)
    (P₀ Q : TensorCompIdx (E := E) r s)
    (D : TransportDiffeoData (I := I) (M := M) g r s β α P₀ Q)
    {u₁ u₂ : EuclN → ℝ}
    (huv : u₁ =ᵐ[chartL2Measure (I := I) (M := M) β] u₂) :
    (fun y => transportCoeffPushed (I := I) (M := M) g r s β α P₀ Q y *
        u₁ (chartTransitionEuclid (I := I) (M := M) α β y)) =ᵐ[
        chartL2Measure (I := I) (M := M) α]
      fun y => transportCoeffPushed (I := I) (M := M) g r s β α P₀ Q y *
        u₂ (chartTransitionEuclid (I := I) (M := M) α β y) := by
  classical
  set Ωαβ := D.Ωαβ with hΩαβ_def
  have hΩαβ_meas : MeasurableSet Ωαβ :=
    Ωαβ_measurableSet (I := I) (M := M) g r s β α P₀ Q D
  have huv_Ωβα : u₁ =ᵐ[(volume : Measure EuclN).restrict D.Ωβα] u₂ :=
    huv.filter_mono
      (ae_mono (Measure.restrict_mono D.hΩβα_subset_target le_rfl))
  have h_comp_Ωαβ : (fun y => u₁ (D.Φ.toFun y)) =ᵐ[
      (volume : Measure EuclN).restrict Ωαβ]
        fun y => u₂ (D.Φ.toFun y) :=
    D.Φ.toFun_quasiMeasurePreserving.ae_eq huv_Ωβα
  have h_meas_eq : (chartL2Measure (I := I) (M := M) α).restrict Ωαβ =
      (volume : Measure EuclN).restrict Ωαβ :=
    chartL2Measure_restrict_Ωαβ (I := I) (M := M) g r s β α P₀ Q D
  have h_restrict : (fun y => transportCoeffPushed
      (I := I) (M := M) g r s β α P₀ Q y *
        u₁ (chartTransitionEuclid (I := I) (M := M) α β y)) =ᵐ[
      (chartL2Measure (I := I) (M := M) α).restrict Ωαβ]
        fun y => transportCoeffPushed (I := I) (M := M) g r s β α P₀ Q y *
          u₂ (chartTransitionEuclid (I := I) (M := M) α β y) := by
    rw [h_meas_eq]
    have h_self : ∀ᵐ y ∂((volume : Measure EuclN).restrict Ωαβ), y ∈ Ωαβ :=
      self_mem_ae_restrict hΩαβ_meas
    filter_upwards [h_comp_Ωαβ, h_self] with y hy_eq hy_mem
    have hΦ : chartTransitionEuclid (I := I) (M := M) α β y = D.Φ.toFun y :=
      (D.hΦ_eq y hy_mem).symm
    rw [hΦ, hy_eq]
  refine ae_eq_of_ae_eq_restrict_of_eqOn_compl hΩαβ_meas h_restrict ?_
  intro y hy
  have hcoeff : transportCoeffPushed (I := I) (M := M) g r s β α P₀ Q y = 0 := by
    by_contra hne
    exact hy (D.hsupp_subset y hne)
  rw [hcoeff, zero_mul, zero_mul]

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma transportFun_ae_eq_of_coeFn_ae_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (β α : M)
    (P₀ Q : TensorCompIdx (E := E) r s)
    (D : TransportDiffeoData (I := I) (M := M) g r s β α P₀ Q)
    {f₁ f₂ : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)}
    (h : (f₁ : EuclN → ℝ) =ᵐ[chartL2Measure (I := I) (M := M) β]
      (f₂ : EuclN → ℝ)) :
    transportFun (I := I) (M := M) g r s β α P₀ Q f₁ =ᵐ[
        chartL2Measure (I := I) (M := M) α]
      transportFun (I := I) (M := M) g r s β α P₀ Q f₂ :=
  transportFun_aux_ae_eq (I := I) (M := M) g r s β α P₀ Q D h

private def transportLp
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (β α : M)
    (P₀ Q : TensorCompIdx (E := E) r s)
    (D : TransportDiffeoData (I := I) (M := M) g r s β α P₀ Q)
    (f : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
    Lp ℝ 2 (chartL2Measure (I := I) (M := M) α) :=
  (memLp_transportFun (I := I) (M := M) g r s β α P₀ Q D f).toLp _

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
private lemma transportLp_coeFn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (β α : M)
    (P₀ Q : TensorCompIdx (E := E) r s)
    (D : TransportDiffeoData (I := I) (M := M) g r s β α P₀ Q)
    (f : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
    ((transportLp (I := I) (M := M) g r s β α P₀ Q D f :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) =ᵐ[
        chartL2Measure (I := I) (M := M) α]
      transportFun (I := I) (M := M) g r s β α P₀ Q f := by
  unfold transportLp
  exact MemLp.coeFn_toLp _

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
private lemma transportLp_add
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (β α : M)
    (P₀ Q : TensorCompIdx (E := E) r s)
    (D : TransportDiffeoData (I := I) (M := M) g r s β α P₀ Q)
    (f₁ f₂ : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
    transportLp (I := I) (M := M) g r s β α P₀ Q D (f₁ + f₂) =
      transportLp (I := I) (M := M) g r s β α P₀ Q D f₁ +
        transportLp (I := I) (M := M) g r s β α P₀ Q D f₂ := by
  classical
  apply Lp.ext
  refine (transportLp_coeFn (I := I) (M := M) g r s β α P₀ Q D (f₁ + f₂)).trans ?_
  have h_sum : transportFun (I := I) (M := M) g r s β α P₀ Q (f₁ + f₂) =ᵐ[
      chartL2Measure (I := I) (M := M) α]
        fun y => transportCoeffPushed (I := I) (M := M) g r s β α P₀ Q y *
          (((f₁ : EuclN → ℝ) + (f₂ : EuclN → ℝ))
            (chartTransitionEuclid (I := I) (M := M) α β y)) :=
    transportFun_aux_ae_eq (I := I) (M := M) g r s β α P₀ Q D
      (Lp.coeFn_add f₁ f₂)
  refine h_sum.trans ?_
  have h_split : (fun y => transportCoeffPushed
      (I := I) (M := M) g r s β α P₀ Q y *
        (((f₁ : EuclN → ℝ) + (f₂ : EuclN → ℝ))
          (chartTransitionEuclid (I := I) (M := M) α β y))) =
      fun y => transportFun (I := I) (M := M) g r s β α P₀ Q f₁ y +
        transportFun (I := I) (M := M) g r s β α P₀ Q f₂ y := by
    funext y
    unfold transportFun
    simp only [Pi.add_apply]
    ring
  rw [h_split]
  refine (Filter.EventuallyEq.add
    (transportLp_coeFn (I := I) (M := M) g r s β α P₀ Q D f₁)
    (transportLp_coeFn (I := I) (M := M) g r s β α P₀ Q D f₂)).symm.trans
    (Lp.coeFn_add _ _).symm

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
private lemma transportLp_smul
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (β α : M)
    (P₀ Q : TensorCompIdx (E := E) r s)
    (D : TransportDiffeoData (I := I) (M := M) g r s β α P₀ Q)
    (c : ℝ) (f : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
    transportLp (I := I) (M := M) g r s β α P₀ Q D (c • f) =
      c • transportLp (I := I) (M := M) g r s β α P₀ Q D f := by
  classical
  apply Lp.ext
  refine (transportLp_coeFn (I := I) (M := M) g r s β α P₀ Q D (c • f)).trans ?_
  have h_smul : transportFun (I := I) (M := M) g r s β α P₀ Q (c • f) =ᵐ[
      chartL2Measure (I := I) (M := M) α]
        fun y => transportCoeffPushed (I := I) (M := M) g r s β α P₀ Q y *
          ((c • (f : EuclN → ℝ))
            (chartTransitionEuclid (I := I) (M := M) α β y)) :=
    transportFun_aux_ae_eq (I := I) (M := M) g r s β α P₀ Q D
      (Lp.coeFn_smul c f)
  refine h_smul.trans ?_
  have h_eq : (fun y => transportCoeffPushed
      (I := I) (M := M) g r s β α P₀ Q y *
        ((c • (f : EuclN → ℝ))
          (chartTransitionEuclid (I := I) (M := M) α β y))) =
      fun y => c • transportFun (I := I) (M := M) g r s β α P₀ Q f y := by
    funext y
    unfold transportFun
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [h_eq]
  refine ((transportLp_coeFn (I := I) (M := M) g r s β α P₀ Q D f).const_smul
    c).symm.trans (Lp.coeFn_smul c _).symm

private def transportLpLin
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (β α : M)
    (P₀ Q : TensorCompIdx (E := E) r s)
    (D : TransportDiffeoData (I := I) (M := M) g r s β α P₀ Q) :
    Lp ℝ 2 (chartL2Measure (I := I) (M := M) β) →ₗ[ℝ]
      Lp ℝ 2 (chartL2Measure (I := I) (M := M) α) where
  toFun f := transportLp (I := I) (M := M) g r s β α P₀ Q D f
  map_add' f₁ f₂ := transportLp_add (I := I) (M := M) g r s β α P₀ Q D f₁ f₂
  map_smul' c f := transportLp_smul (I := I) (M := M) g r s β α P₀ Q D c f

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
@[simp] private lemma transportLpLin_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (β α : M)
    (P₀ Q : TensorCompIdx (E := E) r s)
    (D : TransportDiffeoData (I := I) (M := M) g r s β α P₀ Q)
    (f : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
    transportLpLin (I := I) (M := M) g r s β α P₀ Q D f =
      transportLp (I := I) (M := M) g r s β α P₀ Q D f := rfl

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
private lemma transportLpLin_norm_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (β α : M)
    (P₀ Q : TensorCompIdx (E := E) r s)
    (D : TransportDiffeoData (I := I) (M := M) g r s β α P₀ Q) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ f : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β),
        ‖transportLpLin (I := I) (M := M) g r s β α P₀ Q D f‖ ≤ K * ‖f‖ := by
  classical
  obtain ⟨K, hK_nn, hK⟩ :=
    exists_eLpNorm_transportFun_bound (I := I) (M := M) g r s β α P₀ Q D
  refine ⟨K, hK_nn, fun f => ?_⟩
  have h_norm_eq : ‖transportLpLin (I := I) (M := M) g r s β α P₀ Q D f‖ =
      (eLpNorm (transportFun (I := I) (M := M) g r s β α P₀ Q f) 2
        (chartL2Measure (I := I) (M := M) α)).toReal := by
    rw [transportLpLin_apply]
    unfold transportLp
    exact MeasureTheory.Lp.norm_toLp _ _
  rw [h_norm_eq]
  have h_f_norm : ‖f‖ = (eLpNorm (f : EuclN → ℝ) 2
      (chartL2Measure (I := I) (M := M) β)).toReal := by
    rw [Lp.norm_def]
  have h_rhs_ne_top :
      ENNReal.ofReal K *
        eLpNorm (f : EuclN → ℝ) 2 (chartL2Measure (I := I) (M := M) β) ≠
          (⊤ : ℝ≥0∞) :=
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (Lp.memLp f).2).ne
  have h_toReal_le :
      (eLpNorm (transportFun (I := I) (M := M) g r s β α P₀ Q f) 2
        (chartL2Measure (I := I) (M := M) α)).toReal ≤
        (ENNReal.ofReal K *
          eLpNorm (f : EuclN → ℝ) 2
            (chartL2Measure (I := I) (M := M) β)).toReal :=
    ENNReal.toReal_mono h_rhs_ne_top (hK f)
  refine h_toReal_le.trans ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hK_nn, h_f_norm]

private def transportDiffeoData
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (β α : M)
    (P₀ Q : TensorCompIdx (E := E) r s) :
    TransportDiffeoData (I := I) (M := M) g r s β α P₀ Q :=
  (exists_transportDiffeoData (I := I) (M := M) g r s β α P₀ Q).some

def chartTransitionTransportCLM
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (β α : M)
    (P₀ Q : TensorCompIdx (E := E) r s) :
    Lp ℝ 2 (chartL2Measure (I := I) (M := M) β) →L[ℝ]
      Lp ℝ 2 (chartL2Measure (I := I) (M := M) α) :=
  (transportLpLin (I := I) (M := M) g r s β α P₀ Q
    (transportDiffeoData (I := I) (M := M) g r s β α P₀ Q)).mkContinuous
    (transportLpLin_norm_le (I := I) (M := M) g r s β α P₀ Q
      (transportDiffeoData (I := I) (M := M) g r s β α P₀ Q)).choose
    (transportLpLin_norm_le (I := I) (M := M) g r s β α P₀ Q
      (transportDiffeoData (I := I) (M := M) g r s β α P₀ Q)).choose_spec.2

omit [CompleteSpace E] in
lemma chartTransitionTransportCLM_coeFn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (β α : M)
    (P₀ Q : TensorCompIdx (E := E) r s)
    (f : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
    ((chartTransitionTransportCLM (I := I) (M := M) g r s β α P₀ Q f :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) =ᵐ[
        chartL2Measure (I := I) (M := M) α]
      transportFun (I := I) (M := M) g r s β α P₀ Q f := by
  have h_eq : chartTransitionTransportCLM (I := I) (M := M) g r s β α P₀ Q f =
      transportLp (I := I) (M := M) g r s β α P₀ Q
        (transportDiffeoData (I := I) (M := M) g r s β α P₀ Q) f := by
    unfold chartTransitionTransportCLM
    rw [LinearMap.mkContinuous_apply, transportLpLin_apply]
  rw [h_eq]
  exact transportLp_coeFn (I := I) (M := M) g r s β α P₀ Q
    (transportDiffeoData (I := I) (M := M) g r s β α P₀ Q) f

omit [CompleteSpace E] in
theorem chartTransitionTransportCLM_coeFn_aeEq
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (β α : M)
    (P₀ Q : TensorCompIdx (E := E) r s)
    (f : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
    ((chartTransitionTransportCLM (I := I) (M := M) g r s β α P₀ Q f :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) =ᵐ[
        chartL2Measure (I := I) (M := M) α]
      (fun y => chartPushedRaw (I := I) (M := M) α
          (transportCoeffManifold (I := I) (M := M) g r s β α P₀ Q) y *
        (f : EuclN → ℝ) (chartTransitionEuclid (I := I) (M := M) α β y)) := by
  refine (chartTransitionTransportCLM_coeFn
    (I := I) (M := M) g r s β α P₀ Q f).trans ?_
  refine Filter.EventuallyEq.of_eq ?_
  funext y
  rfl

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma transportFun_tensorChartComponent_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (β α : M)
    (S : SmoothCcTensor g r s)
    (P₀ Q : TensorCompIdx (E := E) r s) :
    (fun y => transportCoeffPushed (I := I) (M := M) g r s β α P₀ Q y *
        tensorChartComponent (I := I) (M := M) g r s S β Q.1 Q.2
          (chartTransitionEuclid (I := I) (M := M) α β y)) =
      chartPushedRaw (I := I) (M := M) α
        (fun x => transportCoeffManifold (I := I) (M := M) g r s β α P₀ Q x *
          tensorChartComponentPou (I := I) (M := M) g r s S β Q.1 Q.2 x) := by
  classical
  funext y
  by_cases hy : y ∈ chartTargetEuclid (I := I) (M := M) α
  · set z : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hz_def
    have hsymm_target : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
      rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
      exact hy
    have h_rhs : chartPushedRaw (I := I) (M := M) α
        (fun x => transportCoeffManifold (I := I) (M := M) g r s β α P₀ Q x *
          tensorChartComponentPou (I := I) (M := M) g r s S β Q.1 Q.2 x) y =
        transportCoeffManifold (I := I) (M := M) g r s β α P₀ Q z *
          tensorChartComponentPou (I := I) (M := M) g r s S β Q.1 Q.2 z := by
      rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy, ← hz_def]
    have h_coeff_push : transportCoeffPushed
        (I := I) (M := M) g r s β α P₀ Q y =
          transportCoeffManifold (I := I) (M := M) g r s β α P₀ Q z := by
      unfold transportCoeffPushed
      rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy, ← hz_def]
    rw [h_rhs, h_coeff_push]
    by_cases hcoeff : transportCoeffManifold (I := I) (M := M) g r s β α P₀ Q z = 0
    · rw [hcoeff, zero_mul, zero_mul]
    · have hz_supp : z ∈ transportSupportSet (I := I) (M := M) α β :=
        tsupport_transportCoeffManifold_subset (I := I) (M := M) g r s β α P₀ Q
          (subset_tsupport _ (Function.mem_support.mpr hcoeff))
      have hz_chartα : z ∈ (chartAt H α).source :=
        transportSupportSet_subset_sourceα (I := I) (M := M) α β hz_supp
      have hz_chartβ : z ∈ (chartAt H β).source :=
        transportSupportSet_subset_sourceβ (I := I) (M := M) α β hz_supp
      have hy_eq_image : (toEuclidean (E := E)) (extChartAt I α z) = y := by
        rw [hz_def, (extChartAt I α).right_inv hsymm_target]
        exact (toEuclidean (E := E)).apply_symm_apply y
      have hT_eq : chartTransitionEuclid (I := I) (M := M) α β y =
          (toEuclidean (E := E)) (extChartAt I β z) := by
        rw [← hy_eq_image]
        exact chartTransitionEuclid_eq_chartα_image (I := I) (M := M) α β hz_chartα
      rw [hT_eq, tensorChartComponent_def]
      have hz_extβ_src : z ∈ (extChartAt I β).source := by
        rw [extChartAt_source (I := I)]; exact hz_chartβ
      have h_imageβ_mem :
          (toEuclidean (E := E)) (extChartAt I β z) ∈
            chartTargetEuclid (I := I) (M := M) β := by
        refine ⟨extChartAt I β z, ?_, rfl⟩
        exact (extChartAt I β).map_source hz_extβ_src
      rw [chartPushedRaw_apply_of_mem (I := I) (M := M) β _ h_imageβ_mem]
      rw [(toEuclidean (E := E)).symm_apply_apply,
        (extChartAt I β).left_inv hz_extβ_src]
  · have h_lhs : transportCoeffPushed (I := I) (M := M) g r s β α P₀ Q y = 0 := by
      unfold transportCoeffPushed
      exact chartPushedRaw_apply_of_notMem (I := I) (M := M) α _ hy
    rw [h_lhs, zero_mul,
      chartPushedRaw_apply_of_notMem (I := I) (M := M) α _ hy]

omit [CompleteSpace E] in
theorem chartTransitionTransportCLM_coeFn_smooth
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (β α : M)
    (S : SmoothCcTensor g r s)
    (P₀ Q : TensorCompIdx (E := E) r s) :
    ((chartTransitionTransportCLM (I := I) (M := M) g r s β α P₀ Q
        (tensorL2ChartComponent (I := I) (M := M) g r s
          (S : TensorL2 r s g) β Q) :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) =ᵐ[
        chartL2Measure (I := I) (M := M) α]
      chartPushedRaw (I := I) (M := M) α
        (fun x => transportCoeffManifold (I := I) (M := M) g r s β α P₀ Q x *
          tensorChartComponentPou (I := I) (M := M) g r s S β Q.1 Q.2 x) := by
  classical
  refine (chartTransitionTransportCLM_coeFn (I := I) (M := M) g r s β α P₀ Q
    (tensorL2ChartComponent (I := I) (M := M) g r s
      (S : TensorL2 r s g) β Q)).trans ?_
  have h_comp : transportFun (I := I) (M := M) g r s β α P₀ Q
      (tensorL2ChartComponent (I := I) (M := M) g r s
        (S : TensorL2 r s g) β Q) =ᵐ[chartL2Measure (I := I) (M := M) α]
        fun y => transportCoeffPushed (I := I) (M := M) g r s β α P₀ Q y *
          tensorChartComponent (I := I) (M := M) g r s S β Q.1 Q.2
            (chartTransitionEuclid (I := I) (M := M) α β y) :=
    transportFun_aux_ae_eq (I := I) (M := M) g r s β α P₀ Q
      (transportDiffeoData (I := I) (M := M) g r s β α P₀ Q)
      (tensorL2ChartComponent_smoothToTensorL2_coeFn
        (I := I) (M := M) g r s S β Q)
  refine h_comp.trans ?_
  rw [transportFun_tensorChartComponent_eq (I := I) (M := M) g r s β α S P₀ Q]

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
