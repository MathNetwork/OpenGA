import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.AbstractChartPull


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators Matrix
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open DifferentialGeometry.Analysis.Laplacian.MetricExtension hiding chartTargetEuclid
open DifferentialGeometry.Analysis.Laplacian.ChartMeasureEquiv

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

private def pouWeightTsupport (α : M) : Set M :=
  tsupport (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma pouWeightTsupport_isCompact (α : M) :
    IsCompact (pouWeightTsupport (I := I) (M := M) α) :=
  (isClosed_tsupport _).isCompact

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma pouWeightTsupport_subset_source (α : M) :
    pouWeightTsupport (I := I) (M := M) α ⊆ (chartAt H α).source :=
  DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M α

private def cutoffKernelSet (α : M) : Set M :=
  (exists_compact_closed_between (pouWeightTsupport_isCompact (I := I) (M := M) α)
    (chartAt H α).open_source
    (pouWeightTsupport_subset_source (I := I) (M := M) α)).choose

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma cutoffKernelSet_isCompact (α : M) :
    IsCompact (cutoffKernelSet (I := I) (M := M) α) :=
  (exists_compact_closed_between (pouWeightTsupport_isCompact (I := I) (M := M) α)
    (chartAt H α).open_source
    (pouWeightTsupport_subset_source (I := I) (M := M) α)).choose_spec.1

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma cutoffKernelSet_isClosed (α : M) :
    IsClosed (cutoffKernelSet (I := I) (M := M) α) :=
  (exists_compact_closed_between (pouWeightTsupport_isCompact (I := I) (M := M) α)
    (chartAt H α).open_source
    (pouWeightTsupport_subset_source (I := I) (M := M) α)).choose_spec.2.1

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma pouWeightTsupport_subset_interior_cutoffKernelSet (α : M) :
    pouWeightTsupport (I := I) (M := M) α ⊆
      interior (cutoffKernelSet (I := I) (M := M) α) :=
  (exists_compact_closed_between (pouWeightTsupport_isCompact (I := I) (M := M) α)
    (chartAt H α).open_source
    (pouWeightTsupport_subset_source (I := I) (M := M) α)).choose_spec.2.2.1

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma cutoffKernelSet_subset_source (α : M) :
    cutoffKernelSet (I := I) (M := M) α ⊆ (chartAt H α).source :=
  (exists_compact_closed_between (pouWeightTsupport_isCompact (I := I) (M := M) α)
    (chartAt H α).open_source
    (pouWeightTsupport_subset_source (I := I) (M := M) α)).choose_spec.2.2.2

def chartKernelCutoff (α : M) : C^∞⟮I, M; ℝ⟯ :=
  (exists_contMDiffMap_one_nhds_of_subset_interior (n := (⊤ : ℕ∞)) I
    (isClosed_tsupport
      (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x))
    (pouWeightTsupport_subset_interior_cutoffKernelSet (I := I) (M := M) α)).choose

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma chartKernelCutoff_eventually_one (α : M) :
    ∀ᶠ x in 𝓝ˢ (pouWeightTsupport (I := I) (M := M) α),
      (chartKernelCutoff (I := I) (M := M) α : M → ℝ) x = 1 :=
  (exists_contMDiffMap_one_nhds_of_subset_interior (n := (⊤ : ℕ∞)) I
    (isClosed_tsupport
      (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x))
    (pouWeightTsupport_subset_interior_cutoffKernelSet
      (I := I) (M := M) α)).choose_spec.1

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma chartKernelCutoff_zero_off_cutoffKernelSet (α : M) :
    ∀ x, x ∉ cutoffKernelSet (I := I) (M := M) α →
      (chartKernelCutoff (I := I) (M := M) α : M → ℝ) x = 0 :=
  (exists_contMDiffMap_one_nhds_of_subset_interior (n := (⊤ : ℕ∞)) I
    (isClosed_tsupport
      (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x))
    (pouWeightTsupport_subset_interior_cutoffKernelSet
      (I := I) (M := M) α)).choose_spec.2.1

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma chartKernelCutoff_mem_Icc (α : M) :
    ∀ x, (chartKernelCutoff (I := I) (M := M) α : M → ℝ) x ∈ Set.Icc (0 : ℝ) 1 :=
  (exists_contMDiffMap_one_nhds_of_subset_interior (n := (⊤ : ℕ∞)) I
    (isClosed_tsupport
      (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x))
    (pouWeightTsupport_subset_interior_cutoffKernelSet
      (I := I) (M := M) α)).choose_spec.2.2

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem chartKernelCutoff_eqOn_one (α : M) :
    Set.EqOn ((chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯) : M → ℝ) 1
      (tsupport
        (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) := by
  intro x hx
  exact (chartKernelCutoff_eventually_one (I := I) (M := M) α).self_of_nhdsSet x hx

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem chartKernelCutoff_abs_le_one (α : M) (x : M) :
    |(chartKernelCutoff (I := I) (M := M) α : M → ℝ) x| ≤ 1 := by
  have h := chartKernelCutoff_mem_Icc (I := I) (M := M) α x
  rw [abs_le]
  exact ⟨le_trans (by norm_num) h.1, h.2⟩

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma chartKernelCutoff_tsupport_subset_source (α : M) :
    tsupport ((chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯) : M → ℝ) ⊆
      (chartAt H α).source := by
  refine Subset.trans ?_ (cutoffKernelSet_subset_source (I := I) (M := M) α)
  refine closure_minimal ?_ (cutoffKernelSet_isClosed (I := I) (M := M) α)
  intro x hx
  rw [Function.mem_support] at hx
  by_contra hx_notin
  exact hx (chartKernelCutoff_zero_off_cutoffKernelSet (I := I) (M := M) α x hx_notin)

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem chartKernelCutoff_hasCompactSupport (α : M) :
    HasCompactSupport
      ((chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯) : M → ℝ) := by
  refine HasCompactSupport.of_support_subset_isCompact
    (cutoffKernelSet_isCompact (I := I) (M := M) α) ?_
  intro x hx
  rw [Function.mem_support] at hx
  by_contra hx_notin
  exact hx (chartKernelCutoff_zero_off_cutoffKernelSet (I := I) (M := M) α x hx_notin)

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma chartKernelCutoff_tsupport_isCompact (α : M) :
    IsCompact
      (tsupport
        ((chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯) : M → ℝ)) :=
  chartKernelCutoff_hasCompactSupport (I := I) (M := M) α

def cutoffComponentScalar
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    M → ℝ :=
  fun x : M => ((chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x *
    tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx x

def cutoffComponentEuclid
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    EuclN → ℝ :=
  chartPushedRaw (I := I) (M := M) α
    (cutoffComponentScalar (I := I) (M := M) g r s S α Idx Jdx)

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma cutoffComponentScalar_tsupport_subset_source
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tsupport (cutoffComponentScalar (I := I) (M := M) g r s S α Idx Jdx) ⊆
      (chartAt H α).source := by
  refine Subset.trans ?_ (chartKernelCutoff_tsupport_subset_source (I := I) (M := M) α)
  unfold cutoffComponentScalar
  exact tsupport_smul_subset_left
    (f := fun x : M => ((chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯) :
      M → ℝ) x)
    (g := tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma cutoffComponentScalar_hasCompactSupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    HasCompactSupport (cutoffComponentScalar (I := I) (M := M) g r s S α Idx Jdx) := by
  refine HasCompactSupport.of_support_subset_isCompact
    (chartKernelCutoff_tsupport_isCompact (I := I) (M := M) α) ?_
  intro x hx
  rw [Function.mem_support] at hx
  refine subset_tsupport _ ?_
  rw [Function.mem_support]
  intro hcut_zero
  exact hx (by unfold cutoffComponentScalar; rw [hcut_zero, zero_mul])

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma cutoffComponentScalar_contMDiff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ContMDiff I (𝓘(ℝ, ℝ)) ∞
      (cutoffComponentScalar (I := I) (M := M) g r s S α Idx Jdx) := by
  classical
  intro x
  by_cases hx_chart : x ∈ (chartAt H α).source
  · have hcut : ContMDiff I (𝓘(ℝ, ℝ)) ∞
        (fun y : M => ((chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯) :
          M → ℝ) y) :=
      (chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯).contMDiff
    have hRaw_on := tensorChartComponentRaw_contMDiffOn_chart_source
      (I := I) (M := M) g r s S α Idx Jdx
    have hRaw_at : ContMDiffAt I (𝓘(ℝ, ℝ)) ∞
        (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx) x :=
      hRaw_on.contMDiffAt
        (IsOpen.mem_nhds (chartAt H α).open_source hx_chart)
    exact (hcut.contMDiffAt).mul hRaw_at
  · have hsupp_sub := cutoffComponentScalar_tsupport_subset_source
      (I := I) (M := M) g r s S α Idx Jdx
    have hx_notin : x ∉ tsupport (cutoffComponentScalar (I := I) (M := M)
        g r s S α Idx Jdx) := fun h => hx_chart (hsupp_sub h)
    apply ContMDiffAt.congr_of_eventuallyEq
      (f := fun _ : M => (0 : ℝ)) contMDiffAt_const
    have hopen : IsOpen
        (tsupport (cutoffComponentScalar (I := I) (M := M)
          g r s S α Idx Jdx))ᶜ :=
      isClosed_tsupport _ |>.isOpen_compl
    filter_upwards [hopen.mem_nhds hx_notin] with y hy
    have hy_notin : y ∉ Function.support (cutoffComponentScalar (I := I) (M := M)
        g r s S α Idx Jdx) := fun h_in => hy (subset_tsupport _ h_in)
    by_contra hne
    exact hy_notin hne

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma cutoffComponentScalar_continuous
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    Continuous (cutoffComponentScalar (I := I) (M := M) g r s S α Idx Jdx) :=
  (cutoffComponentScalar_contMDiff (I := I) (M := M) g r s S α Idx Jdx).continuous

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma cutoffComponentScalar_measurable
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    Measurable (cutoffComponentScalar (I := I) (M := M) g r s S α Idx Jdx) :=
  (cutoffComponentScalar_continuous (I := I) (M := M) g r s S α Idx Jdx).measurable

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma cutoffComponentEuclid_eq_chartPushedRaw
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    cutoffComponentEuclid (I := I) (M := M) g r s S α Idx Jdx =
      chartPushedRaw I α
        (cutoffComponentScalar (I := I) (M := M) g r s S α Idx Jdx) := rfl

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma cutoffComponentEuclid_apply_of_mem
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    cutoffComponentEuclid (I := I) (M := M) g r s S α Idx Jdx y =
      cutoffComponentScalar (I := I) (M := M) g r s S α Idx Jdx
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) := by
  rw [cutoffComponentEuclid_eq_chartPushedRaw]
  exact chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma cutoffComponentEuclid_apply_of_notMem
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {y : EuclN} (hy : y ∉ chartTargetEuclid (I := I) (M := M) α) :
    cutoffComponentEuclid (I := I) (M := M) g r s S α Idx Jdx y = 0 := by
  rw [cutoffComponentEuclid_eq_chartPushedRaw]
  exact chartPushedRaw_apply_of_notMem (I := I) (M := M) α _ hy

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma cutoffComponentEuclid_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (cutoffComponentEuclid (I := I) (M := M) g r s S α Idx Jdx)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have hcut_extsrc : ContMDiffOn I 𝓘(ℝ) ∞
      (cutoffComponentScalar (I := I) (M := M) g r s S α Idx Jdx)
      ((extChartAt I α).source) :=
    (cutoffComponentScalar_contMDiff (I := I) (M := M)
      g r s S α Idx Jdx).contMDiffOn
  have hsymm : ContMDiffOn 𝓘(ℝ, E) I ∞ (extChartAt I α).symm
      (extChartAt I α).target := contMDiffOn_extChartAt_symm (I := I) α
  have hmaps : Set.MapsTo (extChartAt I α).symm (extChartAt I α).target
      (extChartAt I α).source := fun y hy => (extChartAt I α).map_target hy
  have hcomp_E : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) ∞
      ((cutoffComponentScalar (I := I) (M := M) g r s S α Idx Jdx) ∘
        (extChartAt I α).symm)
      (extChartAt I α).target :=
    hcut_extsrc.comp hsymm hmaps
  have hcontDiff_E : ContDiffOn ℝ ∞
      ((cutoffComponentScalar (I := I) (M := M) g r s S α Idx Jdx) ∘
        (extChartAt I α).symm)
      (extChartAt I α).target :=
    hcomp_E.contDiffOn
  have hcomp_eucl : ContDiffOn ℝ ∞
      (((cutoffComponentScalar (I := I) (M := M) g r s S α Idx Jdx) ∘
          (extChartAt I α).symm) ∘
        ((toEuclidean (E := E)).symm : EuclN → E))
      (chartTargetEuclid (I := I) (M := M) α) := by
    refine hcontDiff_E.comp ?_ ?_
    · exact (toEuclidean (E := E)).symm.contDiff.contDiffOn
    · rintro z ⟨w, hw_target, rfl⟩
      have h_eq : (toEuclidean (E := E)).symm (toEuclidean (E := E) w) = w :=
        (toEuclidean (E := E)).symm_apply_apply w
      rw [h_eq]; exact hw_target
  refine hcomp_eucl.congr (fun y hy => ?_)
  rw [cutoffComponentEuclid_apply_of_mem (I := I) (M := M) g r s S α Idx Jdx hy]
  rfl

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma cutoffComponentEuclid_continuousOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ContinuousOn (cutoffComponentEuclid (I := I) (M := M) g r s S α Idx Jdx)
      (chartTargetEuclid (I := I) (M := M) α) :=
  (cutoffComponentEuclid_contDiffOn (I := I) (M := M) g r s S α Idx Jdx).continuousOn

omit [CompleteSpace E] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma sq_norm_le_const_mul_chartTensorInner_on_compact
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    {K_M : Set M} (hK_M_compact : IsCompact K_M)
    (hK_M_sub : K_M ⊆ (trivializationAt E (TangentSpace I) α).baseSet) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ b : M, b ∈ K_M → ∀ T : TensorRSModel r s ℝ E,
        ‖T‖ ^ 2 ≤ K * chartTensorInnerPointwise_rs_model
          (I := I) (M := M) g r s α b T T := by
  classical
  haveI : ProperSpace (TensorRSModel r s ℝ E) :=
    FiniteDimensional.proper_real (TensorRSModel r s ℝ E)
  set S_T : Set (TensorRSModel r s ℝ E) :=
    Metric.sphere (0 : TensorRSModel r s ℝ E) 1 with hS_T_def
  have hS_T_compact : IsCompact S_T :=
    isCompact_sphere (0 : TensorRSModel r s ℝ E) 1
  have hS_T_norm : ∀ T : TensorRSModel r s ℝ E, T ∈ S_T → ‖T‖ = 1 := by
    intro T hT
    rwa [hS_T_def, Metric.mem_sphere, dist_zero_right] at hT
  have hS_T_ne_zero : ∀ T : TensorRSModel r s ℝ E, T ∈ S_T → T ≠ 0 := by
    intro T hT hT0
    have h1 : ‖T‖ = 1 := hS_T_norm T hT
    rw [hT0, norm_zero] at h1
    exact one_ne_zero h1.symm
  set K : Set (M × TensorRSModel r s ℝ E) := K_M ×ˢ S_T with hK_def
  have hK_compact : IsCompact K := hK_M_compact.prod hS_T_compact
  set Q : M × TensorRSModel r s ℝ E → ℝ := fun bT =>
    chartTensorInnerPointwise_rs_model (I := I) (M := M)
      g r s α bT.1 bT.2 bT.2 with hQ_def
  have hQ_contOn_full :
      ContinuousOn Q
        ((trivializationAt E (TangentSpace I) α).baseSet ×ˢ Set.univ) :=
    chartTensorInnerPointwise_rs_model_quadratic_continuousOn
      (I := I) (M := M) g r s α
  have hK_sub_full :
      K ⊆ ((trivializationAt E (TangentSpace I) α).baseSet ×ˢ Set.univ) :=
    fun p hp => ⟨hK_M_sub hp.1, Set.mem_univ _⟩
  have hQ_contOn : ContinuousOn Q K := hQ_contOn_full.mono hK_sub_full
  obtain ⟨ε, hε_pos, h_lb⟩ :
      ∃ ε : ℝ, 0 < ε ∧
        ∀ b : M, b ∈ K_M → ∀ T : TensorRSModel r s ℝ E, ‖T‖ = 1 →
          ε ≤ chartTensorInnerPointwise_rs_model (I := I) (M := M)
            g r s α b T T := by
    by_cases hK_ne : K.Nonempty
    · obtain ⟨p₀, hp₀_mem, hp₀_min⟩ :=
        hK_compact.exists_isMinOn hK_ne hQ_contOn
      have hp₀_base : p₀.1 ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
        hK_M_sub hp₀_mem.1
      have hp₀_ne : p₀.2 ≠ 0 := hS_T_ne_zero p₀.2 hp₀_mem.2
      have hp₀_pos : 0 < Q p₀ :=
        chartTensorInnerPointwise_rs_model_pos_of_ne_zero
          (I := I) (M := M) g r s α hp₀_base hp₀_ne
      refine ⟨Q p₀, hp₀_pos, ?_⟩
      intro b hb T hT_norm
      have hT_mem : T ∈ S_T := by
        rw [hS_T_def, Metric.mem_sphere, dist_zero_right]; exact hT_norm
      exact hp₀_min (⟨hb, hT_mem⟩ : (b, T) ∈ K)
    · refine ⟨1, one_pos, ?_⟩
      intro b hb T hT_norm
      have hT_mem : T ∈ S_T := by
        rw [hS_T_def, Metric.mem_sphere, dist_zero_right]; exact hT_norm
      exact absurd ⟨(b, T), ⟨hb, hT_mem⟩⟩ hK_ne
  refine ⟨ε⁻¹, le_of_lt (inv_pos.mpr hε_pos), ?_⟩
  intro b hb T
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    hK_M_sub hb
  have hQ_nn : 0 ≤ chartTensorInnerPointwise_rs_model
      (I := I) (M := M) g r s α b T T :=
    chartTensorInnerPointwise_rs_model_nonneg
      (I := I) (M := M) g r s α hb_base T
  by_cases hT0 : T = 0
  · subst hT0
    have h_left : ‖(0 : TensorRSModel r s ℝ E)‖ ^ 2 = 0 := by simp
    have h_right : chartTensorInnerPointwise_rs_model
        (I := I) (M := M) g r s α b (0 : TensorRSModel r s ℝ E)
          (0 : TensorRSModel r s ℝ E) = 0 := by
      have h := chartTensorInnerPointwise_rs_model_smul_left
        (I := I) (M := M) g r s α b 0 (0 : TensorRSModel r s ℝ E)
        (0 : TensorRSModel r s ℝ E)
      rwa [zero_smul, zero_mul] at h
    rw [h_left, h_right, mul_zero]
  · have hT_pos : 0 < ‖T‖ := norm_pos_iff.mpr hT0
    letI : NormSMulClass ℝ (TensorRSModel r s ℝ E) :=
      NormedSpace.toNormSMulClass
    set T' : TensorRSModel r s ℝ E := ‖T‖⁻¹ • T with hT'_def
    have hT'_norm : ‖T'‖ = 1 := by
      rw [hT'_def, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hT_pos]
      field_simp
    have h_T' : ε ≤ chartTensorInnerPointwise_rs_model
        (I := I) (M := M) g r s α b T' T' := h_lb b hb T' hT'_norm
    have h_bilin :
        chartTensorInnerPointwise_rs_model (I := I) (M := M) g r s α b T' T' =
          (‖T‖⁻¹ * ‖T‖⁻¹) * chartTensorInnerPointwise_rs_model
            (I := I) (M := M) g r s α b T T := by
      rw [hT'_def,
        chartTensorInnerPointwise_rs_model_smul_left
          (I := I) (M := M) g r s α b ‖T‖⁻¹ T (‖T‖⁻¹ • T),
        chartTensorInnerPointwise_rs_model_smul_right
          (I := I) (M := M) g r s α b ‖T‖⁻¹ T T]
      ring
    rw [h_bilin] at h_T'
    have h_sq_pos : 0 < ‖T‖ ^ 2 := by positivity
    have h_mul : ε * ‖T‖ ^ 2 ≤
        ((‖T‖⁻¹ * ‖T‖⁻¹) * chartTensorInnerPointwise_rs_model
          (I := I) (M := M) g r s α b T T) * ‖T‖ ^ 2 :=
      mul_le_mul_of_nonneg_right h_T' (le_of_lt h_sq_pos)
    have h_rhs :
        ((‖T‖⁻¹ * ‖T‖⁻¹) * chartTensorInnerPointwise_rs_model
          (I := I) (M := M) g r s α b T T) * ‖T‖ ^ 2 =
          chartTensorInnerPointwise_rs_model (I := I) (M := M) g r s α b T T := by
      rw [show ‖T‖ ^ 2 = ‖T‖ * ‖T‖ from by ring]
      field_simp
    rw [h_rhs] at h_mul
    rw [show ε⁻¹ * chartTensorInnerPointwise_rs_model
        (I := I) (M := M) g r s α b T T =
        chartTensorInnerPointwise_rs_model
          (I := I) (M := M) g r s α b T T / ε from by rw [div_eq_inv_mul]]
    exact (le_div_iff₀ hε_pos).mpr (by linarith [h_mul])

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma chartTensorInner_tensorTrivProj_eq_tensorInner
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    chartTensorInnerPointwise_rs_model (I := I) (M := M) g r s α b
        (tensorTrivProj (I := I) (M := M) g r s S α b)
        (tensorTrivProj (I := I) (M := M) g r s S α b) =
      tensorInnerPointwise (I := I) (M := M) g r s b
        (S.toFun b) (S.toFun b) := by
  rw [chartTensorInnerPointwise_rs_model_eq_tensorInnerPointwise
    (I := I) (M := M) g r s α hb _ _,
    tensorTrivProj_eq_chartRSTwistInv_toFun (I := I) (M := M) g r s α S hb,
    chartRSTwist_chartRSTwistInv (I := I) (M := M) α hb r s (S.toFun b)]

omit [CompleteSpace E] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
lemma cutoffComponentScalar_sq_le_const_mul_tensorInner
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensor g r s)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E))
        (b : M),
        (cutoffComponentScalar (I := I) (M := M)
            g r s S α Idx Jdx b) ^ 2 ≤
          C * tensorInnerPointwise (I := I) (M := M) g r s b
            (S.toFun b) (S.toFun b) := by
  classical
  have hKC_compact : IsCompact
      (tsupport ((chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯) :
        M → ℝ)) :=
    chartKernelCutoff_tsupport_isCompact (I := I) (M := M) α
  have hKC_sub : tsupport
      ((chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯) : M → ℝ) ⊆
      (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source]
    exact chartKernelCutoff_tsupport_subset_source (I := I) (M := M) α
  obtain ⟨K, hK_nn, h_norm⟩ :=
    sq_norm_le_const_mul_chartTensorInner_on_compact
      (I := I) (M := M) (E := E) g r s α hKC_compact hKC_sub
  set C_proj : ℝ := chartComponentProjectionUniformBound (E := E) r s
  have hC_proj_nn : 0 ≤ C_proj :=
    chartComponentProjectionUniformBound_nonneg (E := E) r s
  refine ⟨C_proj ^ 2 * K, mul_nonneg (sq_nonneg _) hK_nn, ?_⟩
  intro S Idx Jdx b
  set χ : M → ℝ := fun x : M =>
    ((chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x with hχ_def
  set T : TensorRSModel r s ℝ E :=
    tensorTrivProj (I := I) (M := M) g r s S α b with hT_def
  set P_IJ : TensorRSModel r s ℝ E →L[ℝ] ℝ :=
    tensorChartComponentProjection (E := E) r s Idx Jdx with hP_def
  have hQ_nn : 0 ≤ tensorInnerPointwise (I := I) (M := M) g r s b
      (S.toFun b) (S.toFun b) :=
    tensorInnerPointwise_nonneg (I := I) (M := M) g r s b _
  have hsc_eq : cutoffComponentScalar (I := I) (M := M)
      g r s S α Idx Jdx b = χ b * P_IJ T := rfl
  by_cases hb : b ∈ tsupport χ
  · have hχ_abs_le_one : |χ b| ≤ 1 :=
      chartKernelCutoff_abs_le_one (I := I) (M := M) α b
    have h_proj_le : ‖P_IJ T‖ ≤ C_proj * ‖T‖ :=
      (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right
          (tensorChartComponentProjection_norm_le_uniform (E := E) r s Idx Jdx)
          (norm_nonneg _))
    have h_proj_sq_le : (P_IJ T) ^ 2 ≤ C_proj ^ 2 * ‖T‖ ^ 2 := by
      have h_abs : (P_IJ T) ^ 2 = ‖P_IJ T‖ ^ 2 := by
        rw [Real.norm_eq_abs, sq_abs]
      rw [h_abs]
      have hsq := mul_self_le_mul_self (norm_nonneg _) h_proj_le
      have h_rhs : (C_proj * ‖T‖) * (C_proj * ‖T‖) = C_proj ^ 2 * ‖T‖ ^ 2 := by
        ring
      have h_lhs : ‖P_IJ T‖ * ‖P_IJ T‖ = ‖P_IJ T‖ ^ 2 := by rw [sq]
      linarith [hsq, h_lhs.symm.le, h_rhs.symm.le, h_lhs.le, h_rhs.le]
    have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
      hKC_sub hb
    have h_triv_sq_le : ‖T‖ ^ 2 ≤ K *
        tensorInnerPointwise (I := I) (M := M) g r s b
          (S.toFun b) (S.toFun b) := by
      have h := h_norm b hb T
      rwa [hT_def, chartTensorInner_tensorTrivProj_eq_tensorInner
        (I := I) (M := M) g r s α S hb_base] at h
    have hC_proj_sq_nn : 0 ≤ C_proj ^ 2 := sq_nonneg _
    have h_chain_sq : (P_IJ T) ^ 2 ≤
        C_proj ^ 2 *
          (K * tensorInnerPointwise (I := I) (M := M) g r s b
              (S.toFun b) (S.toFun b)) :=
      h_proj_sq_le.trans
        (mul_le_mul_of_nonneg_left h_triv_sq_le hC_proj_sq_nn)
    have h_χ_sq_le_one : χ b ^ 2 ≤ 1 := by
      rw [show χ b ^ 2 = |χ b| ^ 2 from by rw [sq_abs]]
      have h := mul_le_mul hχ_abs_le_one hχ_abs_le_one (abs_nonneg _)
        (by norm_num)
      rw [sq]; linarith
    have h_KQ_nn : 0 ≤
        K * tensorInnerPointwise (I := I) (M := M) g r s b
          (S.toFun b) (S.toFun b) := mul_nonneg hK_nn hQ_nn
    have h_factored : χ b ^ 2 * (P_IJ T) ^ 2 ≤
        1 *
          (C_proj ^ 2 *
            (K * tensorInnerPointwise (I := I) (M := M) g r s b
                (S.toFun b) (S.toFun b))) :=
      mul_le_mul h_χ_sq_le_one h_chain_sq (sq_nonneg _)
        (by linarith [mul_nonneg hC_proj_sq_nn h_KQ_nn])
    rw [hsc_eq, mul_pow]
    have h_rhs_rearr :
        1 *
          (C_proj ^ 2 *
            (K * tensorInnerPointwise (I := I) (M := M) g r s b
                (S.toFun b) (S.toFun b))) =
          C_proj ^ 2 * K *
            tensorInnerPointwise (I := I) (M := M) g r s b
              (S.toFun b) (S.toFun b) := by ring
    linarith [h_factored, h_rhs_rearr.le, h_rhs_rearr.symm.le]
  · have hχ_zero : χ b = 0 := by
      by_contra hne
      exact hb (subset_tsupport _ hne)
    rw [hsc_eq, hχ_zero, zero_mul]
    have hC_sq_nn : 0 ≤ C_proj ^ 2 := sq_nonneg _
    have h_RHS_nn : 0 ≤ C_proj ^ 2 * K *
        tensorInnerPointwise (I := I) (M := M) g r s b
          (S.toFun b) (S.toFun b) := by
      have heq : C_proj ^ 2 * K *
          tensorInnerPointwise (I := I) (M := M) g r s b
            (S.toFun b) (S.toFun b) =
          C_proj ^ 2 *
            (K * tensorInnerPointwise (I := I) (M := M) g r s b
              (S.toFun b) (S.toFun b)) := by ring
      have := mul_nonneg hC_sq_nn (mul_nonneg hK_nn hQ_nn)
      linarith [heq.le, heq.symm.le]
    rw [show (0 : ℝ) ^ 2 = 0 from by ring]
    exact h_RHS_nn

private lemma sq_eLpNorm_two_eq_lintegral_enorm_sq
    {β : Type*} [MeasurableSpace β] (μ : Measure β) (f : β → ℝ) :
    (eLpNorm f 2 μ) ^ 2 = ∫⁻ x, (‖f x‖ₑ : ℝ≥0∞) ^ 2 ∂μ := by
  classical
  have h2_ne_zero : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have h2_ne_top : (2 : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞) := by norm_num
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (μ := μ) h2_ne_zero h2_ne_top]
  have h2_toReal : ((2 : ℝ≥0∞)).toReal = 2 := by show ENNReal.toReal 2 = 2; rfl
  rw [h2_toReal]
  have h_inner_eq : ∫⁻ x, (‖f x‖ₑ : ℝ≥0∞) ^ (2 : ℝ) ∂μ =
      ∫⁻ x, (‖f x‖ₑ : ℝ≥0∞) ^ 2 ∂μ := by
    refine lintegral_congr_ae ?_
    filter_upwards with x
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast]
  rw [h_inner_eq, ← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul]
  norm_num

private lemma eLpNorm_two_le_ofReal_sqrt
    {β : Type*} [MeasurableSpace β] {μ : Measure β} {f : β → ℝ}
    {Sv : ℝ} (hSv : 0 ≤ Sv)
    (h_sq : (eLpNorm f 2 μ) ^ 2 ≤ ENNReal.ofReal Sv) :
    eLpNorm f 2 μ ≤ ENNReal.ofReal (Real.sqrt Sv) := by
  have h_xpow : eLpNorm f 2 μ =
      ((eLpNorm f 2 μ) ^ 2) ^ ((1 : ℝ) / 2) := by
    rw [← ENNReal.rpow_natCast (eLpNorm f 2 μ) 2, ← ENNReal.rpow_mul]
    norm_num
  have h_pow : eLpNorm f 2 μ ≤ (ENNReal.ofReal Sv) ^ ((1 : ℝ) / 2) := by
    conv_lhs => rw [h_xpow]
    exact ENNReal.rpow_le_rpow h_sq (by norm_num)
  have h_rhs : (ENNReal.ofReal Sv) ^ ((1 : ℝ) / 2) =
      ENNReal.ofReal (Real.sqrt Sv) := by
    rw [show Sv = Real.sqrt Sv * Real.sqrt Sv from (Real.mul_self_sqrt hSv).symm,
      ENNReal.ofReal_mul (Real.sqrt_nonneg _),
      show (ENNReal.ofReal (Real.sqrt Sv)) * (ENNReal.ofReal (Real.sqrt Sv)) =
        (ENNReal.ofReal (Real.sqrt Sv)) ^ 2 from by ring,
      ← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul]
    norm_num
  rwa [h_rhs] at h_pow

omit [CompleteSpace E] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma cutoffComponentScalar_eLpNorm_le_uniform
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensor g r s)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        eLpNorm (cutoffComponentScalar (I := I) (M := M) g r s S α Idx Jdx) 2
            (riemannianVolumeMeasure (I := I) (M := M) g) ≤
          ENNReal.ofReal C *
            ENNReal.ofReal (tensorL2Norm (I := I) (M := M) g r s S.toFun) := by
  classical
  obtain ⟨C, hC_nn, h_pt⟩ :=
    cutoffComponentScalar_sq_le_const_mul_tensorInner
      (I := I) (M := M) (E := E) g r s α
  refine ⟨Real.sqrt C, Real.sqrt_nonneg _, ?_⟩
  intro S Idx Jdx
  set f : M → ℝ := cutoffComponentScalar (I := I) (M := M) g r s S α Idx Jdx
    with hf_def
  set μ : Measure M := riemannianVolumeMeasure (I := I) (M := M) g with hμ_def
  have h_inner_int :
      Integrable (fun b : M => tensorInnerPointwise (I := I) (M := M) g r s b
        (S.toFun b) (S.toFun b)) μ :=
    SmoothCcTensor.integrable_inner_cross (I := I) (M := M) S S
  have h_inner_nn :
      0 ≤ tensorL2Inner (I := I) (M := M) g r s S.toFun S.toFun := by
    unfold tensorL2Inner
    exact integral_nonneg (fun b =>
      tensorInnerPointwise_nonneg (I := I) (M := M) g r s b _)
  have h_norm_sq :
      tensorL2Inner (I := I) (M := M) g r s S.toFun S.toFun =
        (tensorL2Norm (I := I) (M := M) g r s S.toFun) ^ 2 := by
    unfold tensorL2Norm
    rw [sq, Real.mul_self_sqrt h_inner_nn]
  have h_sq_bound :
      (eLpNorm f 2 μ) ^ 2 ≤
        ENNReal.ofReal (C *
          tensorL2Inner (I := I) (M := M) g r s S.toFun S.toFun) := by
    have h_pt_enn : ∀ b : M,
        (‖f b‖ₑ : ℝ≥0∞) ^ 2 ≤
          ENNReal.ofReal (C * tensorInnerPointwise (I := I) (M := M)
            g r s b (S.toFun b) (S.toFun b)) := by
      intro b
      rw [show (‖f b‖ₑ : ℝ≥0∞) ^ 2 = ENNReal.ofReal ((f b) ^ 2) from by
        rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _) 2,
          sq_abs]]
      exact ENNReal.ofReal_le_ofReal (h_pt S Idx Jdx b)
    have h_C_smul_int :
        Integrable (fun b : M => C *
          tensorInnerPointwise (I := I) (M := M) g r s b
            (S.toFun b) (S.toFun b)) μ :=
      h_inner_int.const_mul C
    have h_C_smul_nn :
        0 ≤ᵐ[μ] (fun b : M => C * tensorInnerPointwise
          (I := I) (M := M) g r s b (S.toFun b) (S.toFun b)) :=
      Filter.Eventually.of_forall (fun b =>
        mul_nonneg hC_nn
          (tensorInnerPointwise_nonneg (I := I) (M := M) g r s b _))
    rw [sq_eLpNorm_two_eq_lintegral_enorm_sq μ f]
    have h_lint_le :
        ∫⁻ b, (‖f b‖ₑ : ℝ≥0∞) ^ 2 ∂μ ≤
          ∫⁻ b, ENNReal.ofReal (C * tensorInnerPointwise
            (I := I) (M := M) g r s b (S.toFun b) (S.toFun b)) ∂μ :=
      lintegral_mono_ae (Filter.Eventually.of_forall h_pt_enn)
    rw [(MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      h_C_smul_int h_C_smul_nn).symm] at h_lint_le
    rwa [show ∫ b, C * tensorInnerPointwise (I := I) (M := M) g r s b
        (S.toFun b) (S.toFun b) ∂μ =
        C * tensorL2Inner (I := I) (M := M) g r s S.toFun S.toFun from by
      unfold tensorL2Inner; rw [integral_const_mul]] at h_lint_le
  have h_total_nn : 0 ≤ C *
      tensorL2Inner (I := I) (M := M) g r s S.toFun S.toFun :=
    mul_nonneg hC_nn h_inner_nn
  have h_eLp := eLpNorm_two_le_ofReal_sqrt h_total_nn h_sq_bound
  have h_sqrt_factor :
      Real.sqrt (C * tensorL2Inner (I := I) (M := M) g r s S.toFun S.toFun) =
        Real.sqrt C * tensorL2Norm (I := I) (M := M) g r s S.toFun := by
    rw [h_norm_sq, Real.sqrt_mul hC_nn,
      show (tensorL2Norm (I := I) (M := M) g r s S.toFun) ^ 2 =
        tensorL2Norm (I := I) (M := M) g r s S.toFun *
          tensorL2Norm (I := I) (M := M) g r s S.toFun from by ring,
      Real.sqrt_mul_self (tensorL2Norm_nonneg (I := I) (M := M) g r s S.toFun)]
  rw [h_sqrt_factor, ENNReal.ofReal_mul (Real.sqrt_nonneg _)] at h_eLp
  exact h_eLp

def cutoffChartKernel (α : M) : Set E :=
  (extChartAt I α) ''
    (tsupport
      ((chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯) : M → ℝ))

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma cutoffChartKernel_isCompact (α : M) :
    IsCompact (cutoffChartKernel (I := I) (M := M) α) := by
  classical
  refine (chartKernelCutoff_tsupport_isCompact (I := I) (M := M) α).image_of_continuousOn ?_
  refine (continuousOn_extChartAt α).mono ?_
  intro x hx
  rw [extChartAt_source]
  exact chartKernelCutoff_tsupport_subset_source (I := I) (M := M) α hx

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma cutoffChartKernel_subset_target (α : M) :
    cutoffChartKernel (I := I) (M := M) α ⊆ (extChartAt I α).target := by
  classical
  rintro y ⟨x, hx, rfl⟩
  have hx_src : x ∈ (extChartAt I α).source := by
    rw [extChartAt_source]
    exact chartKernelCutoff_tsupport_subset_source (I := I) (M := M) α hx
  exact (extChartAt I α).map_source hx_src

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma cutoffComponentScalar_chartImage_subset_kernel
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    (extChartAt I α) ''
        (tsupport (cutoffComponentScalar (I := I) (M := M)
          g r s S α Idx Jdx)) ⊆
      cutoffChartKernel (I := I) (M := M) α := by
  classical
  refine Set.image_mono ?_
  unfold cutoffComponentScalar
  exact tsupport_smul_subset_left
    (f := fun x : M => ((chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯) :
      M → ℝ) x)
    (g := tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)

omit [CompleteSpace E] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
lemma cutoffComponentEuclid_eLpNorm_le_uniform
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensor g r s)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        eLpNorm (cutoffComponentEuclid (I := I) (M := M) g r s S α Idx Jdx) 2
            (chartL2Measure (I := I) (M := M) α) ≤
          ENNReal.ofReal C * ENNReal.ofReal ‖S‖ := by
  classical
  obtain ⟨C₁, hC₁_nn, h_scalar⟩ :=
    cutoffComponentScalar_eLpNorm_le_uniform (I := I) (M := M) g r s α
  by_cases hker : (cutoffChartKernel (I := I) (M := M) α).Nonempty
  · obtain ⟨C₂, hC₂_pos, h_bridge⟩ :=
      DifferentialGeometry.Analysis.Sobolev.Chart.eLpNorm_chartPushedRaw_le_const_mul_eLpNorm_riemannianMeasure_uniform
        (I := I) (M := M) g α
        (cutoffChartKernel_isCompact (I := I) (M := M) α) hker
        (cutoffChartKernel_subset_target (I := I) (M := M) α)
        (p := 2) (by norm_num) (by norm_num)
    refine ⟨C₂ * C₁, mul_nonneg hC₂_pos.le hC₁_nn, ?_⟩
    intro S Idx Jdx
    rw [cutoffComponentEuclid_eq_chartPushedRaw (I := I) (M := M)
      g r s S α Idx Jdx]
    have h1 :=
      h_bridge
        (cutoffComponentScalar_measurable (I := I) (M := M) g r s S α Idx Jdx)
        (cutoffComponentScalar_tsupport_subset_source
          (I := I) (M := M) g r s S α Idx Jdx)
        (cutoffComponentScalar_chartImage_subset_kernel
          (I := I) (M := M) g r s S α Idx Jdx)
    have h2 := h_scalar S Idx Jdx
    have h_chain :
        eLpNorm (chartPushedRaw I α
            (cutoffComponentScalar (I := I) (M := M)
              g r s S α Idx Jdx)) 2
            ((volume : Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α)) ≤
          ENNReal.ofReal C₂ *
            (ENNReal.ofReal C₁ * ENNReal.ofReal ‖S‖) := by
      refine h1.trans ?_
      gcongr
      rwa [SmoothCcTensor.norm_def (I := I) (M := M)]
    rw [chartL2Measure, ENNReal.ofReal_mul hC₂_pos.le, mul_assoc]
    exact h_chain
  · refine ⟨0, le_refl 0, ?_⟩
    intro S Idx Jdx
    have h_supp_empty :
        ¬ (tsupport (cutoffComponentScalar (I := I) (M := M)
          g r s S α Idx Jdx)).Nonempty := by
      intro h_ne
      exact hker
        ((h_ne.image (extChartAt I α)).mono
          (cutoffComponentScalar_chartImage_subset_kernel
            (I := I) (M := M) g r s S α Idx Jdx))
    have h_scalar_zero :
        cutoffComponentScalar (I := I) (M := M) g r s S α Idx Jdx =
          (fun _ : M => (0 : ℝ)) := by
      funext x
      exact image_eq_zero_of_notMem_tsupport
        (fun hxs => h_supp_empty ⟨x, hxs⟩)
    have h_comp_zero :
        cutoffComponentEuclid (I := I) (M := M) g r s S α Idx Jdx =
          (fun _ : EuclN => (0 : ℝ)) := by
      rw [cutoffComponentEuclid_eq_chartPushedRaw (I := I) (M := M)
        g r s S α Idx Jdx, h_scalar_zero]
      funext y
      by_cases hy : y ∈ chartTargetEuclid (I := I) (M := M) α
      · rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy]
      · rw [chartPushedRaw_apply_of_notMem (I := I) (M := M) α _ hy]
    rw [h_comp_zero, ENNReal.ofReal_zero, zero_mul]
    rw [show (fun _ : EuclN => (0 : ℝ)) = (0 : EuclN → ℝ) from rfl, eLpNorm_zero]

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma cutoffComponentEuclid_memLp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    MemLp (cutoffComponentEuclid (I := I) (M := M) g r s S α Idx Jdx) 2
      (chartL2Measure (I := I) (M := M) α) := by
  classical
  obtain ⟨C, hC_nn, h_bound⟩ :=
    cutoffComponentEuclid_eLpNorm_le_uniform (I := I) (M := M) g r s α
  refine ⟨?_, ?_⟩
  · rw [chartL2Measure]
    exact ContinuousOn.aestronglyMeasurable
      (cutoffComponentEuclid_continuousOn (I := I) (M := M) g r s S α Idx Jdx)
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
        (I := I) (M := M) α).measurableSet
  · refine lt_of_le_of_lt (h_bound S Idx Jdx) ?_
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma cutoffComponentScalar_add
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S₁ S₂ : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    cutoffComponentScalar (I := I) (M := M) g r s (S₁ + S₂) α Idx Jdx =
      (fun x => cutoffComponentScalar (I := I) (M := M) g r s S₁ α Idx Jdx x +
        cutoffComponentScalar (I := I) (M := M) g r s S₂ α Idx Jdx x) := by
  funext x
  unfold cutoffComponentScalar
  have hraw_add :
      tensorChartComponentRaw (I := I) (M := M) g r s (S₁ + S₂) α Idx Jdx x =
        tensorChartComponentRaw (I := I) (M := M) g r s S₁ α Idx Jdx x +
          tensorChartComponentRaw (I := I) (M := M) g r s S₂ α Idx Jdx x := by
    unfold tensorChartComponentRaw tensorTrivProj
    rw [show (S₁ + S₂).toSection x = S₁.toSection x + S₂.toSection x from by
      rw [SmoothCcTensor.toSection_add]; rfl, map_add, map_add]
  rw [hraw_add]; ring

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma cutoffComponentScalar_smul
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (c : ℝ) (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    cutoffComponentScalar (I := I) (M := M) g r s (c • S) α Idx Jdx =
      (fun x => c • cutoffComponentScalar (I := I) (M := M)
        g r s S α Idx Jdx x) := by
  funext x
  unfold cutoffComponentScalar
  have hraw_smul :
      tensorChartComponentRaw (I := I) (M := M) g r s (c • S) α Idx Jdx x =
        c • tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx x := by
    unfold tensorChartComponentRaw tensorTrivProj
    rw [show (c • S).toSection x = c • S.toSection x from by
      rw [SmoothCcTensor.toSection_smul]; rfl, map_smul, map_smul]
  rw [hraw_smul, smul_eq_mul, smul_eq_mul]; ring

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma cutoffComponentEuclid_add
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S₁ S₂ : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    cutoffComponentEuclid (I := I) (M := M) g r s (S₁ + S₂) α Idx Jdx =
      (fun y => cutoffComponentEuclid (I := I) (M := M) g r s S₁ α Idx Jdx y +
        cutoffComponentEuclid (I := I) (M := M) g r s S₂ α Idx Jdx y) := by
  funext y
  rw [cutoffComponentEuclid_eq_chartPushedRaw,
    cutoffComponentScalar_add (I := I) (M := M) g r s S₁ S₂ α Idx Jdx]
  by_cases hy : y ∈ chartTargetEuclid (I := I) (M := M) α
  · rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy,
      cutoffComponentEuclid_apply_of_mem (I := I) (M := M) g r s S₁ α Idx Jdx hy,
      cutoffComponentEuclid_apply_of_mem (I := I) (M := M) g r s S₂ α Idx Jdx hy]
  · rw [chartPushedRaw_apply_of_notMem (I := I) (M := M) α _ hy,
      cutoffComponentEuclid_apply_of_notMem
        (I := I) (M := M) g r s S₁ α Idx Jdx hy,
      cutoffComponentEuclid_apply_of_notMem
        (I := I) (M := M) g r s S₂ α Idx Jdx hy, add_zero]

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma cutoffComponentEuclid_smul
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (c : ℝ) (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    cutoffComponentEuclid (I := I) (M := M) g r s (c • S) α Idx Jdx =
      (fun y => c • cutoffComponentEuclid (I := I) (M := M)
        g r s S α Idx Jdx y) := by
  funext y
  rw [cutoffComponentEuclid_eq_chartPushedRaw,
    cutoffComponentScalar_smul (I := I) (M := M) g r s c S α Idx Jdx]
  by_cases hy : y ∈ chartTargetEuclid (I := I) (M := M) α
  · rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy,
      cutoffComponentEuclid_apply_of_mem (I := I) (M := M) g r s S α Idx Jdx hy]
  · rw [chartPushedRaw_apply_of_notMem (I := I) (M := M) α _ hy,
      cutoffComponentEuclid_apply_of_notMem
        (I := I) (M := M) g r s S α Idx Jdx hy, smul_zero]

private def cutoffComponentLp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    Lp ℝ 2 (chartL2Measure (I := I) (M := M) α) :=
  (cutoffComponentEuclid_memLp (I := I) (M := M) g r s S α Idx Jdx).toLp _

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma cutoffComponentLp_coeFn
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ((cutoffComponentLp (I := I) (M := M) g r s S α Idx Jdx :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) =ᵐ[
        chartL2Measure (I := I) (M := M) α]
      cutoffComponentEuclid (I := I) (M := M) g r s S α Idx Jdx := by
  unfold cutoffComponentLp
  exact MemLp.coeFn_toLp _

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma cutoffComponentLp_add
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S₁ S₂ : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    cutoffComponentLp (I := I) (M := M) g r s (S₁ + S₂) α Idx Jdx =
      cutoffComponentLp (I := I) (M := M) g r s S₁ α Idx Jdx +
        cutoffComponentLp (I := I) (M := M) g r s S₂ α Idx Jdx := by
  classical
  apply Lp.ext
  refine (cutoffComponentLp_coeFn (I := I) (M := M)
    g r s (S₁ + S₂) α Idx Jdx).trans ?_
  rw [cutoffComponentEuclid_add (I := I) (M := M) g r s S₁ S₂ α Idx Jdx]
  refine (Filter.EventuallyEq.add
    (cutoffComponentLp_coeFn (I := I) (M := M) g r s S₁ α Idx Jdx)
    (cutoffComponentLp_coeFn (I := I) (M := M)
      g r s S₂ α Idx Jdx)).symm.trans
    (Lp.coeFn_add _ _).symm

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma cutoffComponentLp_smul
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (c : ℝ) (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    cutoffComponentLp (I := I) (M := M) g r s (c • S) α Idx Jdx =
      c • cutoffComponentLp (I := I) (M := M) g r s S α Idx Jdx := by
  classical
  apply Lp.ext
  refine (cutoffComponentLp_coeFn (I := I) (M := M)
    g r s (c • S) α Idx Jdx).trans ?_
  rw [cutoffComponentEuclid_smul (I := I) (M := M) g r s c S α Idx Jdx]
  refine ((cutoffComponentLp_coeFn (I := I) (M := M)
    g r s S α Idx Jdx).const_smul c).symm.trans (Lp.coeFn_smul c _).symm

private def cutoffComponentLpLin
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : TensorCompIdx (E := E) r s) :
    SmoothCcTensor g r s →ₗ[ℝ] Lp ℝ 2 (chartL2Measure (I := I) (M := M) α) where
  toFun S := cutoffComponentLp (I := I) (M := M) g r s S α P₀.1 P₀.2
  map_add' S₁ S₂ :=
    cutoffComponentLp_add (I := I) (M := M) g r s S₁ S₂ α P₀.1 P₀.2
  map_smul' c S :=
    cutoffComponentLp_smul (I := I) (M := M) g r s c S α P₀.1 P₀.2

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] private lemma cutoffComponentLpLin_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    (S : SmoothCcTensor g r s) :
    cutoffComponentLpLin (I := I) (M := M) g r s α P₀ S =
      cutoffComponentLp (I := I) (M := M) g r s S α P₀.1 P₀.2 := rfl

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma cutoffComponentLpLin_norm_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : TensorCompIdx (E := E) r s) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ S : SmoothCcTensor g r s,
        ‖cutoffComponentLpLin (I := I) (M := M) g r s α P₀ S‖ ≤ C * ‖S‖ := by
  classical
  obtain ⟨C, hC_nn, h_bound⟩ :=
    cutoffComponentEuclid_eLpNorm_le_uniform (I := I) (M := M) g r s α
  refine ⟨C, hC_nn, ?_⟩
  intro S
  have h_norm_eq :
      ‖cutoffComponentLpLin (I := I) (M := M) g r s α P₀ S‖ =
        (eLpNorm (cutoffComponentEuclid (I := I) (M := M)
          g r s S α P₀.1 P₀.2) 2 (chartL2Measure (I := I) (M := M) α)).toReal := by
    rw [cutoffComponentLpLin_apply]
    unfold cutoffComponentLp
    exact MeasureTheory.Lp.norm_toLp _ _
  rw [h_norm_eq]
  have h_eLp := h_bound S P₀.1 P₀.2
  have h_rhs_lt_top :
      ENNReal.ofReal C * ENNReal.ofReal ‖S‖ ≠ (⊤ : ℝ≥0∞) :=
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top).ne
  have h_toReal_le :
      (eLpNorm (cutoffComponentEuclid (I := I) (M := M)
        g r s S α P₀.1 P₀.2) 2 (chartL2Measure (I := I) (M := M) α)).toReal ≤
        (ENNReal.ofReal C * ENNReal.ofReal ‖S‖).toReal :=
    ENNReal.toReal_mono h_rhs_lt_top h_eLp
  refine h_toReal_le.trans ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC_nn,
    ENNReal.toReal_ofReal (norm_nonneg _)]

private def cutoffComponentLpCLM
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : TensorCompIdx (E := E) r s) :
    SmoothCcTensor g r s →L[ℝ] Lp ℝ 2 (chartL2Measure (I := I) (M := M) α) :=
  (cutoffComponentLpLin (I := I) (M := M) g r s α P₀).mkContinuous
    (cutoffComponentLpLin_norm_le (I := I) (M := M) g r s α P₀).choose
    (cutoffComponentLpLin_norm_le (I := I) (M := M) g r s α P₀).choose_spec.2

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] private lemma cutoffComponentLpCLM_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    (S : SmoothCcTensor g r s) :
    cutoffComponentLpCLM (I := I) (M := M) g r s α P₀ S =
      cutoffComponentLp (I := I) (M := M) g r s S α P₀.1 P₀.2 := rfl

private def smoothToTensorL2Cutoff (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    SmoothCcTensor g r s →L[ℝ] TensorL2 r s g :=
  UniformSpace.Completion.toComplL

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
@[simp] private lemma smoothToTensorL2Cutoff_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) :
    smoothToTensorL2Cutoff (I := I) (M := M) g r s S = (S : TensorL2 r s g) := rfl

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma denseRange_smoothToTensorL2Cutoff
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    DenseRange (smoothToTensorL2Cutoff (I := I) (M := M) g r s) := by
  rw [show (smoothToTensorL2Cutoff (I := I) (M := M) g r s :
        SmoothCcTensor g r s → TensorL2 r s g) =
      ((↑) : SmoothCcTensor g r s →
        UniformSpace.Completion (SmoothCcTensor g r s)) from
      UniformSpace.Completion.coe_toComplL]
  exact UniformSpace.Completion.denseRange_coe

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma isUniformInducing_smoothToTensorL2Cutoff
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    IsUniformInducing (smoothToTensorL2Cutoff (I := I) (M := M) g r s) := by
  rw [show (smoothToTensorL2Cutoff (I := I) (M := M) g r s :
        SmoothCcTensor g r s → TensorL2 r s g) =
      ((↑) : SmoothCcTensor g r s →
        UniformSpace.Completion (SmoothCcTensor g r s)) from
      UniformSpace.Completion.coe_toComplL]
  exact UniformSpace.Completion.isUniformInducing_coe (SmoothCcTensor g r s)

def tensorL2ChartComponentCutoff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (u : TensorL2 r s g) (α : M)
    (P₀ : TensorCompIdx (E := E) r s) :
    Lp ℝ 2 (chartL2Measure (I := I) (M := M) α) :=
  ContinuousLinearMap.extend
    (cutoffComponentLpCLM (I := I) (M := M) g r s α P₀)
    (smoothToTensorL2Cutoff (I := I) (M := M) g r s) u

def tensorL2ChartComponentCutoffCLM
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : TensorCompIdx (E := E) r s) :
    TensorL2 r s g →L[ℝ] Lp ℝ 2 (chartL2Measure (I := I) (M := M) α) :=
  ContinuousLinearMap.extend
    (cutoffComponentLpCLM (I := I) (M := M) g r s α P₀)
    (smoothToTensorL2Cutoff (I := I) (M := M) g r s)

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma tensorL2ChartComponentCutoffCLM_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    (u : TensorL2 r s g) :
    tensorL2ChartComponentCutoffCLM (I := I) (M := M) g r s α P₀ u =
      tensorL2ChartComponentCutoff (I := I) (M := M) g r s u α P₀ := rfl

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma tensorL2ChartComponentCutoff_smoothToTensorL2_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (P₀ : TensorCompIdx (E := E) r s) :
    tensorL2ChartComponentCutoff (I := I) (M := M) g r s
        (S : TensorL2 r s g) α P₀ =
      (cutoffComponentEuclid_memLp (I := I) (M := M)
        g r s S α P₀.1 P₀.2).toLp
        (cutoffComponentEuclid (I := I) (M := M) g r s S α P₀.1 P₀.2) := by
  classical
  have h_extend :
      tensorL2ChartComponentCutoff (I := I) (M := M) g r s
          (smoothToTensorL2Cutoff (I := I) (M := M) g r s S) α P₀ =
        cutoffComponentLpCLM (I := I) (M := M) g r s α P₀ S := by
    unfold tensorL2ChartComponentCutoff
    exact ContinuousLinearMap.extend_eq
      (cutoffComponentLpCLM (I := I) (M := M) g r s α P₀)
      (e := smoothToTensorL2Cutoff (I := I) (M := M) g r s)
      (denseRange_smoothToTensorL2Cutoff (I := I) (M := M) g r s)
      (isUniformInducing_smoothToTensorL2Cutoff (I := I) (M := M) g r s) S
  rw [smoothToTensorL2Cutoff_apply] at h_extend
  rw [h_extend, cutoffComponentLpCLM_apply]
  rfl

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
lemma tensorL2ChartComponentCutoff_smoothToTensorL2_coeFn
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (P₀ : TensorCompIdx (E := E) r s) :
    ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
        (S : TensorL2 r s g) α P₀ :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) =ᵐ[
        chartL2Measure (I := I) (M := M) α]
      cutoffComponentEuclid (I := I) (M := M) g r s S α P₀.1 P₀.2 := by
  rw [tensorL2ChartComponentCutoff_smoothToTensorL2_eq (I := I) (M := M)
    g r s S α P₀]
  exact MemLp.coeFn_toLp _

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma cutoffComponentEuclid_eq_cutoff_mul_tensorComponentEuclid
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M) (P : CompIdx E r s)
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    cutoffComponentEuclid (I := I) (M := M) g r s T α P.1 P.2 y =
      ((chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
        tensorComponentEuclid (I := I) (M := M) g r s T α P y := by
  rw [cutoffComponentEuclid_apply_of_mem (I := I) (M := M) g r s T α P.1 P.2 hy,
    tensorComponentEuclid_apply_of_mem (I := I) (M := M) g r s T α P hy]
  rfl

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma cutoff_chartPull_integrand_eq_raw
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Sg T : SmoothCcTensor g r s)
    (hSg : tsupport Sg.toFun ⊆
      tsupport (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x))
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    (∑ P : CompIdx E r s, ∑ Q : CompIdx E r s,
        covChartMetricGram (I := I) (M := M) g r s α P Q y *
          cutoffComponentEuclid (I := I) (M := M) g r s T α P.1 P.2 y *
          tensorComponentEuclid (I := I) (M := M) g r s Sg α Q y) =
      ∑ P : CompIdx E r s, ∑ Q : CompIdx E r s,
        covChartMetricGram (I := I) (M := M) g r s α P Q y *
          tensorComponentEuclid (I := I) (M := M) g r s Sg α P y *
          tensorComponentEuclid (I := I) (M := M) g r s T α Q y := by
  classical
  set b : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hb_def
  set χb : ℝ := ((chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b
    with hχb_def
  have h_lhs_eq :
      (∑ P : CompIdx E r s, ∑ Q : CompIdx E r s,
        covChartMetricGram (I := I) (M := M) g r s α P Q y *
          cutoffComponentEuclid (I := I) (M := M) g r s T α P.1 P.2 y *
          tensorComponentEuclid (I := I) (M := M) g r s Sg α Q y) =
      ∑ P : CompIdx E r s, ∑ Q : CompIdx E r s,
        covChartMetricGram (I := I) (M := M) g r s α P Q y *
          (χb * tensorComponentEuclid (I := I) (M := M) g r s T α P y) *
          tensorComponentEuclid (I := I) (M := M) g r s Sg α Q y := by
    refine Finset.sum_congr rfl (fun P _ => Finset.sum_congr rfl (fun Q _ => ?_))
    rw [cutoffComponentEuclid_eq_cutoff_mul_tensorComponentEuclid
      (I := I) (M := M) g r s T α P hy]
  rw [h_lhs_eq]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun P _ => Finset.sum_congr rfl (fun Q _ => ?_))
  rw [covChartMetricGram_symm (I := I) (M := M) g r s α Q P y]
  by_cases hSg_zero : tensorComponentEuclid (I := I) (M := M) g r s Sg α P y = 0
  · rw [hSg_zero]; ring
  · have hb_supp : b ∈ tsupport Sg.toFun := by
      have hraw_ne :
          tensorChartComponentRaw (I := I) (M := M) g r s Sg α P.1 P.2 b ≠ 0 := by
        intro hzero
        exact hSg_zero (by
          rw [tensorComponentEuclid_apply_of_mem (I := I) (M := M)
            g r s Sg α P hy, ← hb_def, hzero])
      exact tensorChartComponentRaw_tsupport_subset
        (I := I) (M := M) g r s Sg α P.1 P.2 (subset_tsupport _ hraw_ne)
    have hχb_one : χb = 1 :=
      chartKernelCutoff_eqOn_one (I := I) (M := M) α (hSg hb_supp)
    rw [hχb_one]; ring

private noncomputable def chartPullCoeffCutoff
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Sg : SmoothCcTensor g r s) (P : CompIdx E r s) : EuclN → ℝ :=
  fun y => ∑ Q : CompIdx E r s,
    densityOnEuclid (I := I) g α y *
      covChartMetricGram (I := I) (M := M) g r s α P Q y *
      tensorComponentEuclid (I := I) (M := M) g r s Sg α Q y

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] [T2Space M] [SigmaCompactSpace M] in
private lemma chartPullCoeffCutoff_summand_continuous
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Sg : SmoothCcTensor g r s) (P Q : CompIdx E r s)
    (hSg : tsupport Sg.toFun ⊆ (chartAt H α).source) :
    Continuous (fun y : EuclN =>
      densityOnEuclid (I := I) g α y *
        covChartMetricGram (I := I) (M := M) g r s α P Q y *
        tensorComponentEuclid (I := I) (M := M) g r s Sg α Q y) := by
  classical
  have hopen : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) α
  have hcontOn : ContinuousOn (fun y : EuclN =>
      densityOnEuclid (I := I) g α y *
        covChartMetricGram (I := I) (M := M) g r s α P Q y *
        tensorComponentEuclid (I := I) (M := M) g r s Sg α Q y)
      (chartTargetEuclid (I := I) (M := M) α) :=
    (((densityOnEuclid_contDiffOn (I := I) g α).continuousOn).mul
      ((covChartMetricGram_contDiffOn (I := I) (M := M) g r s α P Q).continuousOn)).mul
      ((tensorComponentEuclid_contDiffOn (I := I) (M := M) g r s Sg α Q).continuousOn)
  have hsupp_subset : tsupport (fun y : EuclN =>
      densityOnEuclid (I := I) g α y *
        covChartMetricGram (I := I) (M := M) g r s α P Q y *
        tensorComponentEuclid (I := I) (M := M) g r s Sg α Q y) ⊆
      chartTargetEuclid (I := I) (M := M) α := by
    refine Subset.trans ?_
      (tensorComponentEuclid_tsupport_subset (I := I) (M := M) g r s Sg α Q hSg)
    refine closure_minimal ?_ (isClosed_tsupport _)
    intro y hy
    rw [Function.mem_support] at hy
    refine subset_tsupport _ ?_
    rw [Function.mem_support]
    intro hzero
    exact hy (by rw [hzero, mul_zero])
  exact hcontOn.continuous_of_tsupport_subset hopen hsupp_subset

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma chartPullCoeffCutoff_summand_hasCompactSupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Sg : SmoothCcTensor g r s) (P Q : CompIdx E r s)
    (hSg : tsupport Sg.toFun ⊆ (chartAt H α).source) :
    HasCompactSupport (fun y : EuclN =>
      densityOnEuclid (I := I) g α y *
        covChartMetricGram (I := I) (M := M) g r s α P Q y *
        tensorComponentEuclid (I := I) (M := M) g r s Sg α Q y) := by
  classical
  refine HasCompactSupport.of_support_subset_isCompact
    (tensorComponentEuclid_hasCompactSupport (I := I) (M := M) g r s Sg α Q hSg) ?_
  intro y hy
  rw [Function.mem_support] at hy
  refine subset_tsupport _ ?_
  rw [Function.mem_support]
  intro hzero
  exact hy (by rw [hzero, mul_zero])

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] [T2Space M] [SigmaCompactSpace M] in
private lemma chartPullCoeffCutoff_continuous
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Sg : SmoothCcTensor g r s) (P : CompIdx E r s)
    (hSg : tsupport Sg.toFun ⊆ (chartAt H α).source) :
    Continuous (chartPullCoeffCutoff (I := I) (M := M) g r s α Sg P) := by
  classical
  unfold chartPullCoeffCutoff
  exact continuous_finset_sum _ (fun Q _ =>
    chartPullCoeffCutoff_summand_continuous (I := I) (M := M) g r s α Sg P Q hSg)

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma chartPullCoeffCutoff_hasCompactSupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Sg : SmoothCcTensor g r s) (P : CompIdx E r s)
    (hSg : tsupport Sg.toFun ⊆ (chartAt H α).source) :
    HasCompactSupport (chartPullCoeffCutoff (I := I) (M := M) g r s α Sg P) := by
  classical
  set K : Set EuclN :=
    ⋃ Q : CompIdx E r s, tsupport (fun y : EuclN =>
      densityOnEuclid (I := I) g α y *
        covChartMetricGram (I := I) (M := M) g r s α P Q y *
        tensorComponentEuclid (I := I) (M := M) g r s Sg α Q y) with hK_def
  have hK_compact : IsCompact K := by
    rw [hK_def]
    exact isCompact_iUnion (fun Q =>
      chartPullCoeffCutoff_summand_hasCompactSupport
        (I := I) (M := M) g r s α Sg P Q hSg)
  refine HasCompactSupport.of_support_subset_isCompact hK_compact ?_
  intro y hy
  rw [Function.mem_support] at hy
  rw [hK_def, Set.mem_iUnion]
  by_contra hy_notin
  simp only [not_exists] at hy_notin
  refine hy ?_
  unfold chartPullCoeffCutoff
  refine Finset.sum_eq_zero (fun Q _ => ?_)
  exact image_eq_zero_of_notMem_tsupport (f := fun y : EuclN =>
    densityOnEuclid (I := I) g α y *
      covChartMetricGram (I := I) (M := M) g r s α P Q y *
      tensorComponentEuclid (I := I) (M := M) g r s Sg α Q y) (hy_notin Q)

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] [T2Space M] [SigmaCompactSpace M] in
private lemma chartPullCoeffCutoff_memLp
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Sg : SmoothCcTensor g r s) (P : CompIdx E r s)
    (hSg : tsupport Sg.toFun ⊆ (chartAt H α).source) :
    MemLp (chartPullCoeffCutoff (I := I) (M := M) g r s α Sg P) 2
      (chartL2Measure (I := I) (M := M) α) := by
  haveI : IsFiniteMeasureOnCompacts (chartL2Measure (I := I) (M := M) α) := by
    rw [chartL2Measure]; infer_instance
  exact (chartPullCoeffCutoff_continuous (I := I) (M := M) g r s α Sg P
      hSg).memLp_of_hasCompactSupport
    (chartPullCoeffCutoff_hasCompactSupport (I := I) (M := M) g r s α Sg P hSg)

private noncomputable def chartPullCoeffCutoffLp
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Sg : SmoothCcTensor g r s) (P : CompIdx E r s)
    (hSg : tsupport Sg.toFun ⊆ (chartAt H α).source) :
    Lp ℝ 2 (chartL2Measure (I := I) (M := M) α) :=
  (chartPullCoeffCutoff_memLp (I := I) (M := M) g r s α Sg P hSg).toLp _

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] [T2Space M] [SigmaCompactSpace M] in
private lemma inner_chartPullCoeffCutoffLp_eq_integral
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Sg : SmoothCcTensor g r s) (P : CompIdx E r s)
    (hSg : tsupport Sg.toFun ⊆ (chartAt H α).source)
    (w : Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
    (⟪chartPullCoeffCutoffLp (I := I) (M := M) g r s α Sg P hSg, w⟫_ℝ : ℝ) =
      ∫ y, chartPullCoeffCutoff (I := I) (M := M) g r s α Sg P y *
          (w : EuclN → ℝ) y
        ∂(chartL2Measure (I := I) (M := M) α) := by
  classical
  rw [MeasureTheory.L2.inner_def]
  refine MeasureTheory.integral_congr_ae ?_
  have hcoe : ((chartPullCoeffCutoffLp (I := I) (M := M) g r s α Sg P hSg :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) =ᵐ[
        chartL2Measure (I := I) (M := M) α]
      chartPullCoeffCutoff (I := I) (M := M) g r s α Sg P := by
    unfold chartPullCoeffCutoffLp
    exact MemLp.coeFn_toLp _
  filter_upwards [hcoe] with y hy
  rw [RCLike.inner_apply, conj_trivial, hy, mul_comm]

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma continuous_chartPullCoeffCutoff_pairing
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Sg : SmoothCcTensor g r s) (P : CompIdx E r s)
    (hSg : tsupport Sg.toFun ⊆ (chartAt H α).source) :
    Continuous (fun u : TensorL2 r s g =>
      (⟪chartPullCoeffCutoffLp (I := I) (M := M) g r s α Sg P hSg,
          tensorL2ChartComponentCutoff (I := I) (M := M) g r s u α P⟫_ℝ : ℝ)) := by
  classical
  have hfun : (fun u : TensorL2 r s g =>
      (⟪chartPullCoeffCutoffLp (I := I) (M := M) g r s α Sg P hSg,
          tensorL2ChartComponentCutoff (I := I) (M := M) g r s u α P⟫_ℝ : ℝ)) =
      (fun w : Lp ℝ 2 (chartL2Measure (I := I) (M := M) α) =>
        (⟪chartPullCoeffCutoffLp (I := I) (M := M) g r s α Sg P hSg, w⟫_ℝ : ℝ)) ∘
        (fun u : TensorL2 r s g =>
          tensorL2ChartComponentCutoffCLM (I := I) (M := M) g r s α P u) := by
    funext u
    rw [Function.comp_apply, tensorL2ChartComponentCutoffCLM_apply]
  rw [hfun]
  refine Continuous.comp ?_
    (tensorL2ChartComponentCutoffCLM (I := I) (M := M) g r s α P).continuous
  exact (innerSL ℝ
    (chartPullCoeffCutoffLp (I := I) (M := M) g r s α Sg P hSg)).continuous

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma cutoff_chartPull_integrand_eq_coeff_mul
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Sg : SmoothCcTensor g r s) (u : TensorL2 r s g) (y : EuclN) :
    densityOnEuclid (I := I) g α y *
        (∑ P : CompIdx E r s, ∑ Q : CompIdx E r s,
          covChartMetricGram (I := I) (M := M) g r s α P Q y *
            ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s u α P :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y *
            tensorComponentEuclid (I := I) (M := M) g r s Sg α Q y) =
      ∑ P : CompIdx E r s,
        chartPullCoeffCutoff (I := I) (M := M) g r s α Sg P y *
          ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s u α P :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y := by
  classical
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun P _ => ?_)
  unfold chartPullCoeffCutoff
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun Q _ => ?_)
  ring

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma cutoff_chartPull_summand_integrable
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Sg : SmoothCcTensor g r s) (u : TensorL2 r s g) (P : CompIdx E r s)
    (hSg : tsupport Sg.toFun ⊆ (chartAt H α).source) :
    Integrable (fun y : EuclN =>
        chartPullCoeffCutoff (I := I) (M := M) g r s α Sg P y *
          ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s u α P :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      (chartL2Measure (I := I) (M := M) α) :=
  MemLp.integrable_mul
    (chartPullCoeffCutoff_memLp (I := I) (M := M) g r s α Sg P hSg)
    (Lp.memLp _)

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma cutoff_chartPull_integral_eq_sum_inner
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Sg : SmoothCcTensor g r s) (u : TensorL2 r s g)
    (hSg : tsupport Sg.toFun ⊆ (chartAt H α).source) :
    ∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          (∑ P : CompIdx E r s, ∑ Q : CompIdx E r s,
            covChartMetricGram (I := I) (M := M) g r s α P Q y *
              ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s u α P :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y *
              tensorComponentEuclid (I := I) (M := M) g r s Sg α Q y)
        ∂(volume : Measure EuclN) =
      ∑ P : CompIdx E r s,
        (⟪chartPullCoeffCutoffLp (I := I) (M := M) g r s α Sg P hSg,
            tensorL2ChartComponentCutoff (I := I) (M := M) g r s u α P⟫_ℝ : ℝ) := by
  classical
  rw [show (∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          (∑ P : CompIdx E r s, ∑ Q : CompIdx E r s,
            covChartMetricGram (I := I) (M := M) g r s α P Q y *
              ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s u α P :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y *
              tensorComponentEuclid (I := I) (M := M) g r s Sg α Q y)
        ∂(volume : Measure EuclN)) =
      ∫ y,
        densityOnEuclid (I := I) g α y *
          (∑ P : CompIdx E r s, ∑ Q : CompIdx E r s,
            covChartMetricGram (I := I) (M := M) g r s α P Q y *
              ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s u α P :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y *
              tensorComponentEuclid (I := I) (M := M) g r s Sg α Q y)
        ∂(chartL2Measure (I := I) (M := M) α) from rfl]
  rw [show (fun y : EuclN =>
        densityOnEuclid (I := I) g α y *
          (∑ P : CompIdx E r s, ∑ Q : CompIdx E r s,
            covChartMetricGram (I := I) (M := M) g r s α P Q y *
              ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s u α P :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y *
              tensorComponentEuclid (I := I) (M := M) g r s Sg α Q y)) =
      (fun y : EuclN =>
        ∑ P : CompIdx E r s,
          chartPullCoeffCutoff (I := I) (M := M) g r s α Sg P y *
            ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s u α P :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) from by
    funext y
    exact cutoff_chartPull_integrand_eq_coeff_mul (I := I) (M := M) g r s α Sg u y]
  rw [MeasureTheory.integral_finset_sum (Finset.univ : Finset (CompIdx E r s))
    (fun P _ => cutoff_chartPull_summand_integrable
      (I := I) (M := M) g r s α Sg u P hSg)]
  refine Finset.sum_congr rfl (fun P _ => ?_)
  rw [inner_chartPullCoeffCutoffLp_eq_integral (I := I) (M := M) g r s α Sg P hSg]

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma continuous_cutoff_lhs
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Sg : SmoothCcTensor g r s) :
    Continuous (fun u : TensorL2 r s g =>
      (⟪u, (Sg : TensorL2 r s g)⟫_ℝ : ℝ)) := by
  have hfun : (fun u : TensorL2 r s g =>
      (⟪u, (Sg : TensorL2 r s g)⟫_ℝ : ℝ)) =
      (fun u : TensorL2 r s g =>
        (⟪(Sg : TensorL2 r s g), u⟫_ℝ : ℝ)) := by
    funext u
    exact real_inner_comm _ _
  rw [hfun]
  exact (innerSL ℝ (Sg : TensorL2 r s g)).continuous

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma continuous_cutoff_rhs
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Sg : SmoothCcTensor g r s)
    (hSg : tsupport Sg.toFun ⊆ (chartAt H α).source) :
    Continuous (fun u : TensorL2 r s g =>
      ∑ P : CompIdx E r s,
        (⟪chartPullCoeffCutoffLp (I := I) (M := M) g r s α Sg P hSg,
            tensorL2ChartComponentCutoff (I := I) (M := M) g r s u α P⟫_ℝ : ℝ)) :=
  continuous_finset_sum _ (fun P _ =>
    continuous_chartPullCoeffCutoff_pairing (I := I) (M := M) g r s α Sg P hSg)

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma cutoff_headline_on_smooth
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Sg : SmoothCcTensor g r s)
    (hSg_pou : tsupport Sg.toFun ⊆
      tsupport (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x))
    (hSg_chart : tsupport Sg.toFun ⊆ (chartAt H α).source)
    (T : SmoothCcTensor g r s) :
    (⟪((T : TensorL2 r s g)), (Sg : TensorL2 r s g)⟫_ℝ : ℝ) =
      ∑ P : CompIdx E r s,
        (⟪chartPullCoeffCutoffLp (I := I) (M := M) g r s α Sg P hSg_chart,
            tensorL2ChartComponentCutoff (I := I) (M := M) g r s
              (T : TensorL2 r s g) α P⟫_ℝ : ℝ) := by
  classical
  rw [show (⟪((T : TensorL2 r s g)), (Sg : TensorL2 r s g)⟫_ℝ : ℝ) =
      (⟪T, Sg⟫_ℝ : ℝ) from UniformSpace.Completion.inner_coe _ _,
    SmoothCcTensor.inner_def,
    tensorL2Inner_symm (I := I) (M := M) g r s T.toFun Sg.toFun]
  rw [tensorL2Inner_chartSupported_chart_pull (I := I) (M := M) g r s
    Sg T α hSg_chart]
  have hctE_meas : MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
    (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) α).measurableSet
  rw [setIntegral_congr_fun hctE_meas (fun y hy => by
    rw [← (cutoff_chartPull_integrand_eq_raw (I := I) (M := M) g r s α Sg T
      hSg_pou hy)])]
  have h_ae :
      (fun y : EuclN => densityOnEuclid (I := I) g α y *
        (∑ P : CompIdx E r s, ∑ Q : CompIdx E r s,
          covChartMetricGram (I := I) (M := M) g r s α P Q y *
            cutoffComponentEuclid (I := I) (M := M) g r s T α P.1 P.2 y *
            tensorComponentEuclid (I := I) (M := M) g r s Sg α Q y)) =ᵐ[
          (volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)]
        (fun y : EuclN => densityOnEuclid (I := I) g α y *
          (∑ P : CompIdx E r s, ∑ Q : CompIdx E r s,
            covChartMetricGram (I := I) (M := M) g r s α P Q y *
              ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
                  (T : TensorL2 r s g) α P :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y *
              tensorComponentEuclid (I := I) (M := M) g r s Sg α Q y)) := by
    have hae : ∀ P : CompIdx E r s,
        cutoffComponentEuclid (I := I) (M := M) g r s T α P.1 P.2 =ᵐ[
            (volume : Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α)]
          ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
              (T : TensorL2 r s g) α P :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) :=
      fun P => (tensorL2ChartComponentCutoff_smoothToTensorL2_coeFn
        (I := I) (M := M) g r s T α P).symm
    have hall : ∀ᵐ y ∂((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)),
        ∀ P : CompIdx E r s,
          cutoffComponentEuclid (I := I) (M := M) g r s T α P.1 P.2 y =
            ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
                (T : TensorL2 r s g) α P :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y := by
      rw [MeasureTheory.ae_all_iff]
      exact hae
    filter_upwards [hall] with y hy
    refine congrArg (densityOnEuclid (I := I) g α y * ·) ?_
    refine Finset.sum_congr rfl (fun P _ => Finset.sum_congr rfl (fun Q _ => ?_))
    rw [hy P]
  rw [MeasureTheory.integral_congr_ae h_ae]
  exact cutoff_chartPull_integral_eq_sum_inner (I := I) (M := M) g r s α Sg
    (T : TensorL2 r s g) hSg_chart

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma cutoff_headline_fun_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Sg : SmoothCcTensor g r s)
    (hSg_pou : tsupport Sg.toFun ⊆
      tsupport (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x))
    (hSg_chart : tsupport Sg.toFun ⊆ (chartAt H α).source) :
    (fun u : TensorL2 r s g =>
        (⟪u, (Sg : TensorL2 r s g)⟫_ℝ : ℝ)) =
      (fun u : TensorL2 r s g =>
        ∑ P : CompIdx E r s,
          (⟪chartPullCoeffCutoffLp (I := I) (M := M) g r s α Sg P hSg_chart,
              tensorL2ChartComponentCutoff (I := I) (M := M)
                g r s u α P⟫_ℝ : ℝ)) := by
  classical
  have hdense : DenseRange
      ((↑) : SmoothCcTensor g r s →
        UniformSpace.Completion (SmoothCcTensor g r s)) :=
    UniformSpace.Completion.denseRange_coe
  refine hdense.equalizer
    (continuous_cutoff_lhs (I := I) (M := M) g r s Sg)
    (continuous_cutoff_rhs (I := I) (M := M) g r s α Sg hSg_chart) ?_
  funext T
  exact cutoff_headline_on_smooth (I := I) (M := M) g r s α Sg
    hSg_pou hSg_chart T

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensorL2Inner_cutoff_chartKernelSupported_pull
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (u : TensorL2 r s g) (Sg : SmoothCcTensor g r s)
    (hSg : tsupport Sg.toFun ⊆
      tsupport ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)) :
    (⟪u, (Sg : TensorL2 r s g)⟫_ℝ : ℝ) =
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          (∑ P : CompIdx E r s, ∑ Q : CompIdx E r s,
            covChartMetricGram (I := I) (M := M) g r s α P Q y *
              ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s u α P :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y *
              tensorComponentEuclid (I := I) (M := M) g r s Sg α Q y)
        ∂(volume : Measure EuclN) := by
  classical
  have hSg_chart : tsupport Sg.toFun ⊆ (chartAt H α).source :=
    hSg.trans (DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate
      I M α)
  have hu := congrFun
    (cutoff_headline_fun_eq (I := I) (M := M) g r s α Sg hSg hSg_chart) u
  rw [hu]
  exact (cutoff_chartPull_integral_eq_sum_inner (I := I) (M := M) g r s α Sg u
    hSg_chart).symm

section ElaborationTests

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)

example (α : M) : C^∞⟮I, M; ℝ⟯ := chartKernelCutoff (I := I) (M := M) α

example (u : TensorL2 r s g) (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    Lp ℝ 2 (chartL2Measure (I := I) (M := M) α) :=
  tensorL2ChartComponentCutoff (I := I) (M := M) g r s u α P₀

example (u : TensorL2 r s g) (Sg : SmoothCcTensor g r s) (α : M)
    (hSg : tsupport Sg.toFun ⊆
      tsupport ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)) :
    (⟪u, (Sg : TensorL2 r s g)⟫_ℝ : ℝ) =
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          (∑ P : CompIdx E r s, ∑ Q : CompIdx E r s,
            covChartMetricGram (I := I) (M := M) g r s α P Q y *
              ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s u α P :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y *
              tensorComponentEuclid (I := I) (M := M) g r s Sg α Q y)
        ∂(volume : Measure EuclN) :=
  tensorL2Inner_cutoff_chartKernelSupported_pull
    (I := I) (M := M) g r s α u Sg hSg

end ElaborationTests

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
