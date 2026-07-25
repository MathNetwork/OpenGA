import DifferentialGeometry.Analysis.Sobolev.WithBoundary.Euclidean.Morrey
import DifferentialGeometry.Analysis.Sobolev.WithBoundary.Embedding.Subcritical
import DifferentialGeometry.Analysis.Sobolev.WithBoundary.Embedding.IteratedTower
import DifferentialGeometry.Analysis.Sobolev.WithBoundary.Chart.Defs
import DifferentialGeometry.Analysis.Sobolev.Manifold.MorreyManifold
import DifferentialGeometry.Analysis.Integration.Measure.Family
import DifferentialGeometry.External.DeGiorgi.SobolevSpace.Witnesses
import DifferentialGeometry.Analysis.Sobolev.WithBoundary.Embedding.EvenReflectionExtension


noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Function
open scoped Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace WithBoundary

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]

local notation "EuN" => EuclideanSpace ℝ (Fin n)
local notation "I_hs" => modelWithCornersEuclideanHalfSpace n

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

def chartSmoothExt (α : M) (f : M → ℝ) : EuN → ℝ := by
  classical
  exact fun y =>
    if y ∈ (extChartAt I_hs α).target then
      f ((extChartAt I_hs α).symm y)
    else 0

omit [IsManifold I_hs ∞ M] in
private lemma chartSmoothExt_apply_of_mem_target
    (α : M) (f : M → ℝ) {y : EuN}
    (hy : y ∈ (extChartAt I_hs α).target) :
    chartSmoothExt (n := n) (M := M) α f y =
      f ((extChartAt I_hs α).symm y) := by
  classical
  change (if y ∈ (extChartAt I_hs α).target then
      f ((extChartAt I_hs α).symm y)
    else 0) = f ((extChartAt I_hs α).symm y)
  rw [if_pos hy]

omit [IsManifold I_hs ∞ M] in
private lemma chartSmoothExt_apply_of_notMem_target
    (α : M) (f : M → ℝ) {y : EuN}
    (hy : y ∉ (extChartAt I_hs α).target) :
    chartSmoothExt (n := n) (M := M) α f y = 0 := by
  classical
  change (if y ∈ (extChartAt I_hs α).target then
      f ((extChartAt I_hs α).symm y)
    else 0) = 0
  rw [if_neg hy]

omit [IsManifold I_hs ∞ M] in

private lemma chartSmoothExt_eq_chartPushed_on_target
    (ρ : SmoothPartitionOfUnity M I_hs M Set.univ)
    (α : M) (u : M → ℝ) {y : EuN}
    (hy : y ∈ (extChartAt I_hs α).target) :
    chartSmoothExt (n := n) (M := M) α
        (fun x : M => (ρ α : C^∞⟮I_hs, M; ℝ⟯) x * u x) y =
      chartPushed (n := n) (M := M) ρ α u y := by
  classical
  rw [chartSmoothExt_apply_of_mem_target (n := n) (M := M) α _ hy]
  unfold chartPushed
  rfl

omit [IsManifold (𝓡∂ n) ∞ M] in
private lemma image_extChartAt_tsupport_compact_subset_target
    [CompactSpace M] {f : M → ℝ} {α : M}
    (hf_supp : tsupport f ⊆ (chartAt (EuclideanHalfSpace n) α).source) :
    IsCompact ((extChartAt I_hs α) '' (tsupport f)) ∧
      (extChartAt I_hs α) '' (tsupport f) ⊆ (extChartAt I_hs α).target := by
  classical
  have h_supp_compact : IsCompact (tsupport f) := (isClosed_tsupport _).isCompact
  have h_supp_ext_src : tsupport f ⊆ (extChartAt I_hs α).source := by
    intro x hx
    rw [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
      (I := I_hs) (M := M)]
    exact hf_supp hx
  have h_cont : ContinuousOn (extChartAt I_hs α) (tsupport f) :=
    (continuousOn_extChartAt α).mono h_supp_ext_src
  refine ⟨h_supp_compact.image_of_continuousOn h_cont, ?_⟩
  rintro y ⟨x, hx, rfl⟩
  exact (extChartAt I_hs α).map_source (h_supp_ext_src hx)

omit [IsManifold (𝓡∂ n) ∞ M] in
private lemma chartSmoothExt_eq_zero_off_image_tsupport
    (α : M) {f : M → ℝ}
    (_hf_supp : tsupport f ⊆ (chartAt (EuclideanHalfSpace n) α).source) {y : EuN}
    (hy_off : y ∉ (extChartAt I_hs α) '' (tsupport f)) :
    chartSmoothExt (n := n) (M := M) α f y = 0 := by
  classical
  by_cases hy_target : y ∈ (extChartAt I_hs α).target
  · rw [chartSmoothExt_apply_of_mem_target (n := n) (M := M) α f hy_target]
    by_contra hne
    apply hy_off
    have hsymm_in_supp : (extChartAt I_hs α).symm y ∈ tsupport f :=
      subset_tsupport _ (Function.mem_support.mpr hne)
    have hy_eq : (extChartAt I_hs α) ((extChartAt I_hs α).symm y) = y :=
      (extChartAt I_hs α).right_inv hy_target
    refine ⟨(extChartAt I_hs α).symm y, hsymm_in_supp, hy_eq⟩
  · exact chartSmoothExt_apply_of_notMem_target (n := n) (M := M) α f hy_target

omit [IsManifold (𝓡∂ n) ∞ M] in
private lemma hasCompactSupport_chartSmoothExt
    [CompactSpace M] (α : M) {f : M → ℝ}
    (hf_supp : tsupport f ⊆ (chartAt (EuclideanHalfSpace n) α).source) :
    HasCompactSupport (chartSmoothExt (n := n) (M := M) α f) := by
  classical
  set K : Set EuN := (extChartAt I_hs α) '' (tsupport f) with hK_def
  have hK_compact : IsCompact K :=
    (image_extChartAt_tsupport_compact_subset_target (n := n) (M := M)
      (f := f) (α := α) hf_supp).1
  apply HasCompactSupport.of_support_subset_isCompact hK_compact
  intro y hy_supp
  by_contra hyK
  apply hy_supp
  exact chartSmoothExt_eq_zero_off_image_tsupport
    (n := n) (M := M) α (f := f) hf_supp hyK

omit [IsManifold (𝓡∂ n) ∞ M] in
private lemma tsupport_chartSmoothExt_subset
    [CompactSpace M] (α : M) {f : M → ℝ}
    (hf_supp : tsupport f ⊆ (chartAt (EuclideanHalfSpace n) α).source) :
    tsupport (chartSmoothExt (n := n) (M := M) α f) ⊆
      (extChartAt I_hs α) '' (tsupport f) := by
  classical
  set K : Set EuN := (extChartAt I_hs α) '' (tsupport f) with hK_def
  have hK_compact : IsCompact K :=
    (image_extChartAt_tsupport_compact_subset_target (n := n) (M := M)
      (f := f) (α := α) hf_supp).1
  have hK_closed : IsClosed K := hK_compact.isClosed
  have h_supp_sub : Function.support (chartSmoothExt (n := n) (M := M) α f) ⊆ K := by
    intro y hy
    by_contra hyK
    apply hy
    exact chartSmoothExt_eq_zero_off_image_tsupport
      (n := n) (M := M) α (f := f) hf_supp hyK
  rw [tsupport]
  exact hK_closed.closure_subset_iff.mpr h_supp_sub

private lemma contDiffOn_chartSmoothExt_formula
    (α : M) {f : M → ℝ} (hf : ContMDiff I_hs 𝓘(ℝ, ℝ) ∞ f) :
    ContDiffOn ℝ ∞
        (fun y : EuN => f ((extChartAt I_hs α).symm y))
        (extChartAt I_hs α).target := by
  classical
  exact DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE_contDiffOn
    (I := I_hs) α hf

def chartSmoothExtInteriorSupport
    (α : M) (f : M → ℝ) : Prop :=
  (extChartAt I_hs α) '' (tsupport f) ⊆
    DifferentialGeometry.Analysis.Sobolev.Euclidean.openHalfSpace (d := n)

omit [IsManifold (𝓡∂ n) ∞ M] in
private lemma chartSmoothExtInteriorSupport_image_subset_interior
    {α : M} {f : M → ℝ}
    (hf_supp : tsupport f ⊆ (chartAt (EuclideanHalfSpace n) α).source)
    (h_int : chartSmoothExtInteriorSupport (n := n) (M := M) α f) :
    (extChartAt I_hs α) '' (tsupport f) ⊆
      DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
        (chartTargetEuclid (n := n) (M := M) α) := by
  rintro y ⟨x, hx, rfl⟩
  refine ⟨?_, h_int ⟨x, hx, rfl⟩⟩
  have h_src : x ∈ (extChartAt I_hs α).source := by
    rw [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
      (I := I_hs) (M := M)]
    exact hf_supp hx
  exact (extChartAt I_hs α).map_source h_src

private lemma contDiffAt_chartSmoothExt_of_mem_interior_target
    (α : M) {f : M → ℝ} (hf : ContMDiff I_hs 𝓘(ℝ, ℝ) ∞ f) {y : EuN}
    (hy : y ∈ DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
        (chartTargetEuclid (n := n) (M := M) α)) :
    ContDiffAt ℝ ∞ (chartSmoothExt (n := n) (M := M) α f) y := by
  classical
  have hOpen : IsOpen (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
      (d := n) (chartTargetEuclid (n := n) (M := M) α)) :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace_isOpen
      (chartTargetEuclid_isHalfSpaceRelOpen (n := n) (M := M) α)
  have hy_target : y ∈ (extChartAt I_hs α).target := hy.1
  have hContDiffOn := contDiffOn_chartSmoothExt_formula (n := n) (M := M) α hf
  have h_within : ContDiffWithinAt ℝ ∞
      (fun y : EuN => f ((extChartAt I_hs α).symm y))
      (extChartAt I_hs α).target y := hContDiffOn y hy_target
  have hInt_sub : DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
      (d := n) (chartTargetEuclid (n := n) (M := M) α) ⊆ (extChartAt I_hs α).target := by
    intro z hz
    exact hz.1
  have h_within_int : ContDiffWithinAt ℝ ∞
      (fun y : EuN => f ((extChartAt I_hs α).symm y))
      (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
        (chartTargetEuclid (n := n) (M := M) α)) y :=
    h_within.mono hInt_sub
  have h_contDiffAt : ContDiffAt ℝ ∞
      (fun y : EuN => f ((extChartAt I_hs α).symm y)) y :=
    h_within_int.contDiffAt (hOpen.mem_nhds hy)
  apply h_contDiffAt.congr_of_eventuallyEq
  filter_upwards [hOpen.mem_nhds hy] with z hz
  rw [chartSmoothExt_apply_of_mem_target (n := n) (M := M) α f hz.1]

omit [IsManifold (𝓡∂ n) ∞ M] in
private lemma contDiffAt_chartSmoothExt_of_notMem_image_tsupport
    (α : M) {f : M → ℝ}
    (hf_supp : tsupport f ⊆ (chartAt (EuclideanHalfSpace n) α).source)
    (hf_compact : IsCompact (tsupport f)) {y : EuN}
    (hy_off : y ∉ (extChartAt I_hs α) '' (tsupport f)) :
    ContDiffAt ℝ ∞ (chartSmoothExt (n := n) (M := M) α f) y := by
  classical
  set K : Set EuN := (extChartAt I_hs α) '' (tsupport f) with hK_def
  have hK_compact : IsCompact K := by
    have hsub : tsupport f ⊆ (extChartAt I_hs α).source := by
      intro x hx
      rw [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
        (I := I_hs) (M := M)]
      exact hf_supp hx
    have hcont : ContinuousOn (extChartAt I_hs α) (tsupport f) :=
      (continuousOn_extChartAt α).mono hsub
    exact hf_compact.image_of_continuousOn hcont
  have hK_closed : IsClosed K := hK_compact.isClosed
  have hK_compl_open : IsOpen Kᶜ := hK_closed.isOpen_compl
  have hy_compl : y ∈ Kᶜ := hy_off
  apply ContDiffAt.congr_of_eventuallyEq (f := fun _ : EuN => (0 : ℝ)) contDiffAt_const
  filter_upwards [hK_compl_open.mem_nhds hy_compl] with z hz
  exact chartSmoothExt_eq_zero_off_image_tsupport
    (n := n) (M := M) α (f := f) hf_supp hz

private lemma contDiff_chartSmoothExt
    [CompactSpace M] (α : M) {f : M → ℝ} (hf : ContMDiff I_hs 𝓘(ℝ, ℝ) ∞ f)
    (hf_supp : tsupport f ⊆ (chartAt (EuclideanHalfSpace n) α).source)
    (h_int : chartSmoothExtInteriorSupport (n := n) (M := M) α f) :
    ContDiff ℝ ∞ (chartSmoothExt (n := n) (M := M) α f) := by
  classical
  rw [contDiff_iff_contDiffAt]
  intro y
  set K : Set EuN := (extChartAt I_hs α) '' (tsupport f) with hK_def
  by_cases hyK : y ∈ K
  · have hy_int : y ∈
        DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
          (chartTargetEuclid (n := n) (M := M) α) :=
      chartSmoothExtInteriorSupport_image_subset_interior
        (n := n) (M := M) hf_supp h_int hyK
    exact contDiffAt_chartSmoothExt_of_mem_interior_target
      (n := n) (M := M) α hf hy_int
  · have hf_compact : IsCompact (tsupport f) := (isClosed_tsupport _).isCompact
    exact contDiffAt_chartSmoothExt_of_notMem_image_tsupport
      (n := n) (M := M) α hf_supp hf_compact hyK

omit [IsManifold I_hs ∞ M] in
private lemma tsupport_pou_mul_subset_chart_source
    (ρ : SmoothPartitionOfUnity M I_hs M Set.univ)
    (hρ : ρ.IsSubordinate (fun β : M => (chartAt (EuclideanHalfSpace n) β).source))
    (α : M) (u : M → ℝ) :
    tsupport (fun x : M => (ρ α : C^∞⟮I_hs, M; ℝ⟯) x * u x) ⊆
      (chartAt (EuclideanHalfSpace n) α).source := by
  have h1 : tsupport (fun x : M => (ρ α : C^∞⟮I_hs, M; ℝ⟯) x * u x) ⊆
      tsupport ((ρ α : C^∞⟮I_hs, M; ℝ⟯) : M → ℝ) := by
    have h_eq : (fun x : M => (ρ α : C^∞⟮I_hs, M; ℝ⟯) x * u x) =
        (fun x : M => (ρ α : C^∞⟮I_hs, M; ℝ⟯) x • u x) := by funext x; rfl
    rw [h_eq]
    exact tsupport_smul_subset_left
      (f := fun x : M => ((ρ α : C^∞⟮I_hs, M; ℝ⟯) : M → ℝ) x) (g := u)
  exact h1.trans (hρ α)

private lemma contDiff_chartSmoothExt_pou_mul
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (α : M) (ρ : SmoothPartitionOfUnity M I_hs M Set.univ)
    (hρ : ρ.IsSubordinate (fun β : M => (chartAt (EuclideanHalfSpace n) β).source))
    {u : M → ℝ} (hu : ContMDiff I_hs 𝓘(ℝ, ℝ) ∞ u)
    (h_int : chartSmoothExtInteriorSupport (n := n) (M := M) α
      (fun x : M => (ρ α : C^∞⟮I_hs, M; ℝ⟯) x * u x)) :
    ContDiff ℝ ∞ (chartSmoothExt (n := n) (M := M) α
      (fun x : M => (ρ α : C^∞⟮I_hs, M; ℝ⟯) x * u x)) := by
  set f : M → ℝ := fun x : M => (ρ α : C^∞⟮I_hs, M; ℝ⟯) x * u x with hf_def
  have hf_smooth : ContMDiff I_hs 𝓘(ℝ, ℝ) ∞ f :=
    ((ρ α : C^∞⟮I_hs, M; ℝ⟯).contMDiff).mul hu
  have hf_supp : tsupport f ⊆ (chartAt (EuclideanHalfSpace n) α).source :=
    tsupport_pou_mul_subset_chart_source (n := n) (M := M) ρ hρ α u
  exact contDiff_chartSmoothExt (n := n) (M := M) α hf_smooth hf_supp h_int

omit [IsManifold (𝓡∂ n) ∞ M] in
private lemma hasCompactSupport_chartSmoothExt_pou_mul
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (α : M) (ρ : SmoothPartitionOfUnity M I_hs M Set.univ)
    (hρ : ρ.IsSubordinate (fun β : M => (chartAt (EuclideanHalfSpace n) β).source))
    (u : M → ℝ) :
    HasCompactSupport (chartSmoothExt (n := n) (M := M) α
      (fun x : M => (ρ α : C^∞⟮I_hs, M; ℝ⟯) x * u x)) := by
  set f : M → ℝ := fun x : M => (ρ α : C^∞⟮I_hs, M; ℝ⟯) x * u x with hf_def
  have hf_supp : tsupport f ⊆ (chartAt (EuclideanHalfSpace n) α).source :=
    tsupport_pou_mul_subset_chart_source (n := n) (M := M) ρ hρ α u
  exact hasCompactSupport_chartSmoothExt (n := n) (M := M) α hf_supp

variable [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

private def chartCarrier (α : M) : Set EuN :=
  (extChartAt I_hs α) ''
    (tsupport ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
      : C^∞⟮I_hs, M; ℝ⟯) : M → ℝ))

private lemma chartCarrier_isCompact (α : M) :
    IsCompact (chartCarrier (n := n) (M := M) α) := by
  unfold chartCarrier
  set Tα : Set M := tsupport
    ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
      : C^∞⟮I_hs, M; ℝ⟯) : M → ℝ) with hTα_def
  have hTα_compact : IsCompact Tα := (isClosed_tsupport _).isCompact
  have hTα_chart_src : Tα ⊆ (chartAt (EuclideanHalfSpace n) α).source :=
    DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I_hs M α
  have hTα_ext_src : Tα ⊆ (extChartAt I_hs α).source := by
    intro x hx
    rw [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
      (I := I_hs) (M := M)]
    exact hTα_chart_src hx
  have hcont_ext : ContinuousOn (extChartAt I_hs α) Tα :=
    (continuousOn_extChartAt α).mono hTα_ext_src
  exact hTα_compact.image_of_continuousOn hcont_ext

omit [CompactSpace M] in
private lemma chartCarrier_subset_chartTarget (α : M) :
    chartCarrier (n := n) (M := M) α ⊆ (extChartAt I_hs α).target := by
  unfold chartCarrier
  set Tα : Set M := tsupport
    ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
      : C^∞⟮I_hs, M; ℝ⟯) : M → ℝ) with hTα_def
  have hTα_chart_src : Tα ⊆ (chartAt (EuclideanHalfSpace n) α).source :=
    DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I_hs M α
  have hTα_ext_src : Tα ⊆ (extChartAt I_hs α).source := by
    intro x hx
    rw [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
      (I := I_hs) (M := M)]
    exact hTα_chart_src hx
  rintro y ⟨x, hx, rfl⟩
  exact (extChartAt I_hs α).map_source (hTα_ext_src hx)

private noncomputable def chartRadius (α : M) : ℝ :=
  (((chartCarrier_isCompact (n := n) (M := M) α).isBounded.subset_ball_lt
      0 (0 : EuN)).choose) * 2 + 1

private lemma chartRadius_pos (α : M) : 0 < chartRadius (n := n) (M := M) α := by
  unfold chartRadius
  have h := ((chartCarrier_isCompact (n := n) (M := M) α).isBounded.subset_ball_lt
    0 (0 : EuN)).choose_spec
  linarith [h.1]

private lemma chartCarrier_subset_half_ball (α : M) :
    chartCarrier (n := n) (M := M) α ⊆
      Metric.ball (0 : EuN) (chartRadius (n := n) (M := M) α / 2) := by
  unfold chartRadius
  have h := ((chartCarrier_isCompact (n := n) (M := M) α).isBounded.subset_ball_lt
    0 (0 : EuN)).choose_spec
  have h1 : 0 < (((chartCarrier_isCompact (n := n) (M := M) α).isBounded.subset_ball_lt
      0 (0 : EuN)).choose) := h.1
  have h2 : chartCarrier (n := n) (M := M) α ⊆
      Metric.ball (0 : EuN)
        (((chartCarrier_isCompact (n := n) (M := M) α).isBounded.subset_ball_lt
          0 (0 : EuN)).choose) := h.2
  refine h2.trans ?_
  intro y hy
  rw [Metric.mem_ball] at hy ⊢
  have h_ineq : (((chartCarrier_isCompact (n := n) (M := M) α).isBounded.subset_ball_lt
      0 (0 : EuN)).choose) ≤
      (((chartCarrier_isCompact (n := n) (M := M) α).isBounded.subset_ball_lt
        0 (0 : EuN)).choose * 2 + 1) / 2 := by
    linarith
  linarith

private lemma chartCarrier_subset_full_ball (α : M) :
    chartCarrier (n := n) (M := M) α ⊆
      Metric.ball (0 : EuN) (chartRadius (n := n) (M := M) α) := by
  refine (chartCarrier_subset_half_ball (n := n) (M := M) α).trans ?_
  intro y hy
  rw [Metric.mem_ball] at hy ⊢
  have h := chartRadius_pos (n := n) (M := M) α
  linarith

def AllChartsInteriorSupport (u : M → ℝ) : Prop :=
  ∀ α : M,
    chartSmoothExtInteriorSupport (n := n) (M := M) α
      (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
        : C^∞⟮I_hs, M; ℝ⟯) x * u x)

private lemma tsupport_chartSmoothExt_pou_mul_subset_chartCarrier
    (α : M) (u : M → ℝ) :
    tsupport (chartSmoothExt (n := n) (M := M) α
      (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
        : C^∞⟮I_hs, M; ℝ⟯) x * u x)) ⊆
      chartCarrier (n := n) (M := M) α := by
  classical
  unfold chartCarrier
  set Tα : Set M := tsupport
    ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
      : C^∞⟮I_hs, M; ℝ⟯) : M → ℝ) with hTα_def
  have hTα_chart_src : Tα ⊆ (chartAt (EuclideanHalfSpace n) α).source :=
    DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I_hs M α
  have h_pou_supp_sub_tα : tsupport (fun x : M =>
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
        : C^∞⟮I_hs, M; ℝ⟯) x * u x) ⊆ Tα := by
    have h_eq : (fun x : M =>
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
          : C^∞⟮I_hs, M; ℝ⟯) x * u x) =
        (fun x : M =>
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
            : C^∞⟮I_hs, M; ℝ⟯) x • u x) := by funext x; rfl
    rw [h_eq]
    exact tsupport_smul_subset_left
      (f := fun x : M => ((DifferentialGeometry.Integral.Measure.chartAtlasPOU
        I_hs M α : C^∞⟮I_hs, M; ℝ⟯) : M → ℝ) x) (g := u)
  have h_pou_supp_chart_src : tsupport (fun x : M =>
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
        : C^∞⟮I_hs, M; ℝ⟯) x * u x) ⊆ (chartAt (EuclideanHalfSpace n) α).source :=
    h_pou_supp_sub_tα.trans hTα_chart_src
  have hstep := tsupport_chartSmoothExt_subset (n := n) (M := M) α (f :=
    fun x : M =>
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
        : C^∞⟮I_hs, M; ℝ⟯) x * u x) h_pou_supp_chart_src
  refine hstep.trans ?_
  rintro y ⟨x, hx, rfl⟩
  exact ⟨x, h_pou_supp_sub_tα hx, rfl⟩

private lemma chartSmoothExt_pou_mul_eq_zero_off_half_ball
    (α : M) (u : M → ℝ) {y : EuN}
    (hy : y ∉ Metric.ball (0 : EuN) (chartRadius (n := n) (M := M) α / 2)) :
    chartSmoothExt (n := n) (M := M) α
      (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
        : C^∞⟮I_hs, M; ℝ⟯) x * u x) y = 0 := by
  by_contra hne
  apply hy
  have h_in_supp : y ∈ Function.support (chartSmoothExt (n := n) (M := M) α
      (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
        : C^∞⟮I_hs, M; ℝ⟯) x * u x)) := Function.mem_support.mpr hne
  have h_in_tsupport := subset_tsupport _ h_in_supp
  exact chartCarrier_subset_half_ball (n := n) (M := M) α
    (tsupport_chartSmoothExt_pou_mul_subset_chartCarrier (n := n) (M := M) α u
      h_in_tsupport)

private lemma chartSmoothExt_morrey_sup_uniform
    (α : M) {p : ℝ} (hp : (n : ℝ) < p) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {u : M → ℝ}, ContMDiff I_hs 𝓘(ℝ, ℝ) ∞ u →
        AllChartsInteriorSupport (n := n) (M := M) u →
        ∀ y : EuN, ‖chartSmoothExt (n := n) (M := M) α
          (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
            : C^∞⟮I_hs, M; ℝ⟯) x * u x) y‖ ≤ C *
          ((eLpNorm (chartSmoothExt (n := n) (M := M) α
              (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
                : C^∞⟮I_hs, M; ℝ⟯) x * u x)) (ENNReal.ofReal p)
              (volume.restrict (Metric.ball (0 : EuN) (chartRadius (n := n) (M := M) α)))).toReal +
           (eLpNorm (fun z => ‖fderiv ℝ (chartSmoothExt (n := n) (M := M) α
              (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
                : C^∞⟮I_hs, M; ℝ⟯) x * u x)) z‖) (ENNReal.ofReal p)
             (volume.restrict (Metric.ball (0 : EuN) (chartRadius (n := n) (M := M) α)))).toReal) := by
  classical
  have hR_pos : 0 < chartRadius (n := n) (M := M) α := chartRadius_pos (n := n) (M := M) α
  obtain ⟨C, hC_nn, hbound⟩ :=
    DifferentialGeometry.Analysis.Sobolev.EuclideanMorrey.smooth_morrey_sup_bound_uniform
      (d := n) hp
      (x₀ := (0 : EuN)) (R := chartRadius (n := n) (M := M) α) hR_pos
  refine ⟨C, hC_nn, ?_⟩
  intro u hu h_int y
  set f : EuN → ℝ := chartSmoothExt (n := n) (M := M) α
    (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
      : C^∞⟮I_hs, M; ℝ⟯) x * u x) with hf_def
  have hf_smooth : ContDiff ℝ ∞ f := by
    rw [hf_def]
    exact contDiff_chartSmoothExt_pou_mul (n := n) (M := M) α
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M)
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I_hs M)
      hu (h_int α)
  have hf_smooth_top : ContDiff ℝ (⊤ : ℕ∞) f := by
    have : ContDiff ℝ ∞ f := hf_smooth
    exact this
  by_cases hy_half : y ∈ Metric.ball (0 : EuN) (chartRadius (n := n) (M := M) α / 2)
  · exact hbound hf_smooth_top y hy_half
  · have hf_y_zero : f y = 0 :=
      chartSmoothExt_pou_mul_eq_zero_off_half_ball (n := n) (M := M) α u hy_half
    rw [hf_y_zero, norm_zero]
    have h_nn1 : 0 ≤ (eLpNorm f (ENNReal.ofReal p)
        (volume.restrict (Metric.ball (0 : EuN) (chartRadius (n := n) (M := M) α)))).toReal :=
      ENNReal.toReal_nonneg
    have h_nn2 : 0 ≤ (eLpNorm (fun z => ‖fderiv ℝ f z‖) (ENNReal.ofReal p)
        (volume.restrict (Metric.ball (0 : EuN) (chartRadius (n := n) (M := M) α)))).toReal :=
      ENNReal.toReal_nonneg
    have h_RHS_nn : 0 ≤ C *
        ((eLpNorm f (ENNReal.ofReal p)
            (volume.restrict (Metric.ball (0 : EuN) (chartRadius (n := n) (M := M) α)))).toReal +
         (eLpNorm (fun z => ‖fderiv ℝ f z‖) (ENNReal.ofReal p)
            (volume.restrict (Metric.ball (0 : EuN) (chartRadius (n := n) (M := M) α)))).toReal) := by
      apply mul_nonneg hC_nn
      linarith
    exact h_RHS_nn

omit [IsManifold (𝓡∂ n) ∞ M] [T2Space M] [SigmaCompactSpace M] [CompactSpace M] in
private lemma chartSmoothExt_eq_zero_off_target
    (α : M) (f : M → ℝ) {y : EuN}
    (hy : y ∉ (extChartAt I_hs α).target) :
    chartSmoothExt (n := n) (M := M) α f y = 0 :=
  chartSmoothExt_apply_of_notMem_target (n := n) (M := M) α f hy

omit [NeZero n] in
private lemma fderiv_eq_zero_off_tsupport_subset_closed
    {h : EuN → ℝ} {K : Set EuN} (hK_closed : IsClosed K)
    (hh_supp : tsupport h ⊆ K) {y : EuN} (hy : y ∉ K) :
    fderiv ℝ h y = 0 := by
  have hy_off_tsupp : y ∉ tsupport h := fun hyt => hy (hh_supp hyt)
  have h_compl : Kᶜ ∈ 𝓝 y := hK_closed.isOpen_compl.mem_nhds hy
  have hh_zero_eventually : h =ᶠ[𝓝 y] (fun _ : EuN => (0 : ℝ)) := by
    refine Filter.eventuallyEq_of_mem h_compl ?_
    intro z hz
    have hz_off_tsupp : z ∉ tsupport h := fun hzt => hz (hh_supp hzt)
    exact image_eq_zero_of_notMem_tsupport hz_off_tsupp
  rw [Filter.EventuallyEq.fderiv_eq hh_zero_eventually]
  simp

private lemma eLpNorm_chartSmoothExt_pou_mul_restrict_ball
    (α : M) (u : M → ℝ) (q : ℝ≥0∞) :
    eLpNorm (chartSmoothExt (n := n) (M := M) α
        (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
          : C^∞⟮I_hs, M; ℝ⟯) x * u x)) q
      (volume.restrict (Metric.ball (0 : EuN) (chartRadius (n := n) (M := M) α))) =
      eLpNorm (chartSmoothExt (n := n) (M := M) α
        (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
          : C^∞⟮I_hs, M; ℝ⟯) x * u x)) q volume := by
  classical
  set h : EuN → ℝ := chartSmoothExt (n := n) (M := M) α
    (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
      : C^∞⟮I_hs, M; ℝ⟯) x * u x) with hh_def
  set K : Set EuN := chartCarrier (n := n) (M := M) α with hK_def
  set BR : Set EuN := Metric.ball (0 : EuN) (chartRadius (n := n) (M := M) α)
    with hBR_def
  have hK_closed : IsClosed K := (chartCarrier_isCompact (n := n) (M := M) α).isClosed
  have hK_supp : tsupport h ⊆ K :=
    tsupport_chartSmoothExt_pou_mul_subset_chartCarrier (n := n) (M := M) α u
  have hK_BR : K ⊆ BR :=
    chartCarrier_subset_full_ball (n := n) (M := M) α
  have hBR_meas : MeasurableSet BR := measurableSet_ball
  have h_eq_BR : h = BR.indicator h := by
    funext y
    by_cases hy : y ∈ BR
    · rw [Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem hy]
      have hyK : y ∉ K := fun h2 => hy (hK_BR h2)
      have hy_off_tsupp : y ∉ tsupport h := fun hyt => hyK (hK_supp hyt)
      exact image_eq_zero_of_notMem_tsupport hy_off_tsupp
  calc eLpNorm h q (volume.restrict BR)
      = eLpNorm (BR.indicator h) q volume :=
        (eLpNorm_indicator_eq_eLpNorm_restrict hBR_meas).symm
    _ = eLpNorm h q volume := by rw [← h_eq_BR]

private lemma eLpNorm_norm_fderiv_chartSmoothExt_pou_mul_restrict_ball
    (α : M) (u : M → ℝ) (q : ℝ≥0∞) :
    eLpNorm (fun z : EuN => ‖fderiv ℝ (chartSmoothExt (n := n) (M := M) α
        (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
          : C^∞⟮I_hs, M; ℝ⟯) x * u x)) z‖) q
      (volume.restrict (Metric.ball (0 : EuN) (chartRadius (n := n) (M := M) α))) =
      eLpNorm (fun z : EuN => ‖fderiv ℝ (chartSmoothExt (n := n) (M := M) α
        (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
          : C^∞⟮I_hs, M; ℝ⟯) x * u x)) z‖) q volume := by
  classical
  set h : EuN → ℝ := chartSmoothExt (n := n) (M := M) α
    (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
      : C^∞⟮I_hs, M; ℝ⟯) x * u x) with hh_def
  set K : Set EuN := chartCarrier (n := n) (M := M) α with hK_def
  set BR : Set EuN := Metric.ball (0 : EuN) (chartRadius (n := n) (M := M) α)
    with hBR_def
  have hK_closed : IsClosed K := (chartCarrier_isCompact (n := n) (M := M) α).isClosed
  have hK_supp : tsupport h ⊆ K :=
    tsupport_chartSmoothExt_pou_mul_subset_chartCarrier (n := n) (M := M) α u
  have hK_BR : K ⊆ BR :=
    chartCarrier_subset_full_ball (n := n) (M := M) α
  have hBR_meas : MeasurableSet BR := measurableSet_ball
  set fnNorm : EuN → ℝ := fun z => ‖fderiv ℝ h z‖ with hfnNorm_def
  have h_eq_BR : fnNorm = BR.indicator fnNorm := by
    funext y
    by_cases hy : y ∈ BR
    · rw [Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem hy]
      have hyK : y ∉ K := fun h2 => hy (hK_BR h2)
      have h_fderiv_zero : fderiv ℝ h y = 0 :=
        fderiv_eq_zero_off_tsupport_subset_closed hK_closed hK_supp hyK
      change ‖fderiv ℝ h y‖ = 0
      rw [h_fderiv_zero, norm_zero]
  calc eLpNorm fnNorm q (volume.restrict BR)
      = eLpNorm (BR.indicator fnNorm) q volume :=
        (eLpNorm_indicator_eq_eLpNorm_restrict hBR_meas).symm
    _ = eLpNorm fnNorm q volume := by rw [← h_eq_BR]

omit [CompactSpace M] in

private lemma chartSmoothExt_ae_eq_chartPushed_interior
    (α : M) (u : M → ℝ) :
    chartSmoothExt (n := n) (M := M) α
        (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
          : C^∞⟮I_hs, M; ℝ⟯) x * u x) =ᵐ[volume.restrict
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
          (chartTargetEuclid (n := n) (M := M) α))]
      chartPushed (n := n) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M) α u := by
  have hOpen : IsOpen (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
      (chartTargetEuclid (n := n) (M := M) α)) :=
    interiorHalfSpace_chartTargetEuclid_isOpen (n := n) (M := M) α
  refine (MeasureTheory.ae_restrict_iff' hOpen.measurableSet).mpr ?_
  refine Filter.Eventually.of_forall ?_
  intro y hy
  exact chartSmoothExt_eq_chartPushed_on_target
    (n := n) (M := M) (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M) α u hy.1

omit [CompactSpace M] in
private lemma eLpNorm_chartSmoothExt_interior_eq_eLpNorm_chartPushed_interior
    (α : M) (u : M → ℝ) (q : ℝ≥0∞) :
    eLpNorm (chartSmoothExt (n := n) (M := M) α
        (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
          : C^∞⟮I_hs, M; ℝ⟯) x * u x)) q
      (volume.restrict
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
          (chartTargetEuclid (n := n) (M := M) α))) =
      eLpNorm (chartPushed (n := n) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M) α u) q
        (volume.restrict
          (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
            (chartTargetEuclid (n := n) (M := M) α))) :=
  eLpNorm_congr_ae (chartSmoothExt_ae_eq_chartPushed_interior (n := n) (M := M) α u)

private lemma eLpNorm_chartSmoothExt_pou_mul_restrict_ball_eq_restrict_interior
    {u : M → ℝ} (h_int : AllChartsInteriorSupport (n := n) (M := M) u)
    (α : M) (q : ℝ≥0∞) :
    eLpNorm (chartSmoothExt (n := n) (M := M) α
        (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
          : C^∞⟮I_hs, M; ℝ⟯) x * u x)) q
      (volume.restrict (Metric.ball (0 : EuN) (chartRadius (n := n) (M := M) α))) =
      eLpNorm (chartSmoothExt (n := n) (M := M) α
        (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
          : C^∞⟮I_hs, M; ℝ⟯) x * u x)) q
        (volume.restrict
          (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
            (chartTargetEuclid (n := n) (M := M) α))) := by
  classical
  set h : EuN → ℝ := chartSmoothExt (n := n) (M := M) α
    (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
      : C^∞⟮I_hs, M; ℝ⟯) x * u x) with hh_def
  rw [eLpNorm_chartSmoothExt_pou_mul_restrict_ball (n := n) (M := M) α u q]
  set IntΩ : Set EuN :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
      (chartTargetEuclid (n := n) (M := M) α) with hIntΩ_def
  have hIntΩ_open : IsOpen IntΩ :=
    interiorHalfSpace_chartTargetEuclid_isOpen (n := n) (M := M) α
  have hIntΩ_meas : MeasurableSet IntΩ := hIntΩ_open.measurableSet
  have h_tsupport_in_int : tsupport h ⊆ IntΩ := by
    set f : M → ℝ := fun x : M =>
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
        : C^∞⟮I_hs, M; ℝ⟯) x * u x with hf_def
    have hf_supp_chart_src : tsupport f ⊆ (chartAt (EuclideanHalfSpace n) α).source :=
      tsupport_pou_mul_subset_chart_source (n := n) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I_hs M)
        α u
    have hint_image : (extChartAt I_hs α) '' (tsupport f) ⊆ IntΩ :=
      chartSmoothExtInteriorSupport_image_subset_interior
        (n := n) (M := M) (α := α) (f := f) hf_supp_chart_src (h_int α)
    have h1 : tsupport h ⊆ (extChartAt I_hs α) '' (tsupport f) :=
      tsupport_chartSmoothExt_subset (n := n) (M := M) α hf_supp_chart_src
    exact h1.trans hint_image
  have h_eq_IntΩ : h = IntΩ.indicator h := by
    funext y
    by_cases hy : y ∈ IntΩ
    · rw [Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem hy]
      have hy_off_tsupp : y ∉ tsupport h := fun hyt => hy (h_tsupport_in_int hyt)
      exact image_eq_zero_of_notMem_tsupport hy_off_tsupp
  calc eLpNorm h q volume
      = eLpNorm (IntΩ.indicator h) q volume := by rw [← h_eq_IntΩ]
    _ = eLpNorm h q (volume.restrict IntΩ) :=
        eLpNorm_indicator_eq_eLpNorm_restrict hIntΩ_meas

private lemma eLpNorm_norm_fderiv_chartSmoothExt_pou_mul_restrict_ball_eq_restrict_interior
    {u : M → ℝ} (h_int : AllChartsInteriorSupport (n := n) (M := M) u)
    (α : M) (q : ℝ≥0∞) :
    eLpNorm (fun z : EuN => ‖fderiv ℝ (chartSmoothExt (n := n) (M := M) α
        (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
          : C^∞⟮I_hs, M; ℝ⟯) x * u x)) z‖) q
      (volume.restrict (Metric.ball (0 : EuN) (chartRadius (n := n) (M := M) α))) =
      eLpNorm (fun z : EuN => ‖fderiv ℝ (chartSmoothExt (n := n) (M := M) α
        (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
          : C^∞⟮I_hs, M; ℝ⟯) x * u x)) z‖) q
        (volume.restrict
          (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
            (chartTargetEuclid (n := n) (M := M) α))) := by
  classical
  set h : EuN → ℝ := chartSmoothExt (n := n) (M := M) α
    (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
      : C^∞⟮I_hs, M; ℝ⟯) x * u x) with hh_def
  rw [eLpNorm_norm_fderiv_chartSmoothExt_pou_mul_restrict_ball (n := n) (M := M) α u q]
  set IntΩ : Set EuN :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
      (chartTargetEuclid (n := n) (M := M) α) with hIntΩ_def
  have hIntΩ_open : IsOpen IntΩ :=
    interiorHalfSpace_chartTargetEuclid_isOpen (n := n) (M := M) α
  have hIntΩ_meas : MeasurableSet IntΩ := hIntΩ_open.measurableSet
  have h_tsupport_in_int : tsupport h ⊆ IntΩ := by
    set f : M → ℝ := fun x : M =>
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
        : C^∞⟮I_hs, M; ℝ⟯) x * u x with hf_def
    have hf_supp_chart_src : tsupport f ⊆ (chartAt (EuclideanHalfSpace n) α).source :=
      tsupport_pou_mul_subset_chart_source (n := n) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I_hs M)
        α u
    have hint_image : (extChartAt I_hs α) '' (tsupport f) ⊆ IntΩ :=
      chartSmoothExtInteriorSupport_image_subset_interior
        (n := n) (M := M) (α := α) (f := f) hf_supp_chart_src (h_int α)
    have h1 : tsupport h ⊆ (extChartAt I_hs α) '' (tsupport f) :=
      tsupport_chartSmoothExt_subset (n := n) (M := M) α hf_supp_chart_src
    exact h1.trans hint_image
  have hK_closed_int : IsClosed (tsupport h) := isClosed_tsupport _
  set fnNorm : EuN → ℝ := fun z => ‖fderiv ℝ h z‖ with hfnNorm_def
  have h_eq_IntΩ : fnNorm = IntΩ.indicator fnNorm := by
    funext y
    by_cases hy : y ∈ IntΩ
    · rw [Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem hy]
      have hy_off_tsupp : y ∉ tsupport h := fun hyt => hy (h_tsupport_in_int hyt)
      have h_fderiv_zero : fderiv ℝ h y = 0 := by
        have h_compl : (tsupport h)ᶜ ∈ 𝓝 y :=
          hK_closed_int.isOpen_compl.mem_nhds hy_off_tsupp
        have hh_zero_eventually : h =ᶠ[𝓝 y] (fun _ : EuN => (0 : ℝ)) := by
          refine Filter.eventuallyEq_of_mem h_compl ?_
          intro z hz
          exact image_eq_zero_of_notMem_tsupport hz
        rw [Filter.EventuallyEq.fderiv_eq hh_zero_eventually]
        simp
      change ‖fderiv ℝ h y‖ = 0
      rw [h_fderiv_zero, norm_zero]
  calc eLpNorm fnNorm q volume
      = eLpNorm (IntΩ.indicator fnNorm) q volume := by rw [← h_eq_IntΩ]
    _ = eLpNorm fnNorm q (volume.restrict IntΩ) :=
        eLpNorm_indicator_eq_eLpNorm_restrict hIntΩ_meas

private lemma eLpNorm_chartSmoothExt_ball_le_wkpNormChart
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I_hs M)
    {u : M → ℝ} (h_int : AllChartsInteriorSupport (n := n) (M := M) u)
    (α : M) (q : ℝ≥0∞) :
    eLpNorm (chartSmoothExt (n := n) (M := M) α
        (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
          : C^∞⟮I_hs, M; ℝ⟯) x * u x)) q
      (volume.restrict (Metric.ball (0 : EuN) (chartRadius (n := n) (M := M) α))) ≤
      wkpNormChart (n := n) (M := M) g 1 q u := by
  classical
  rw [eLpNorm_chartSmoothExt_pou_mul_restrict_ball_eq_restrict_interior
    (n := n) (M := M) h_int α q]
  rw [eLpNorm_chartSmoothExt_interior_eq_eLpNorm_chartPushed_interior
    (n := n) (M := M) α u q]
  set Ω : Set EuN := chartTargetEuclid (n := n) (M := M) α with hΩ_def
  have h_zero_eq : eLpNorm (chartPushed (n := n) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M) α u) q
        (volume.restrict
          (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace Ω)) =
      DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace
        (d := n) 0 q
        (chartPushed (n := n) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M) α u) Ω := by
    rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace_zero]
  rw [h_zero_eq]
  have h_le_succ : DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace
      (d := n) 0 q
      (chartPushed (n := n) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M) α u) Ω ≤
      DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace
        (d := n) 1 q
        (chartPushed (n := n) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M) α u) Ω := by
    unfold DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace
    rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_eq_sum 0 q,
        DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_eq_sum 1 q]
    rw [Finset.sum_range_one]
    rw [show (1 : ℕ) + 1 = 2 from rfl]
    rw [show Finset.range 2 = {0, 1} from rfl]
    rw [Finset.sum_insert (by simp), Finset.sum_singleton]
    refine le_add_of_nonneg_right ?_
    exact zero_le _
  refine h_le_succ.trans ?_
  let _ := g
  unfold wkpNormChart
  exact ENNReal.le_tsum α

omit [NeZero n] in
private lemma euN_norm_le_sum_components_norms (w : EuN) :
    ‖w‖ ≤ ∑ i : Fin n, ‖w i‖ := by
  classical
  have h_w_sum :
      w = ∑ i : Fin n, EuclideanSpace.single i (w i) := by
    ext j
    simp [Finset.sum_apply]
  conv_lhs => rw [h_w_sum]
  refine (norm_sum_le _ _).trans ?_
  apply Finset.sum_le_sum
  intro i _
  simp

omit [NeZero n] in
private lemma norm_fderiv_eq_norm_partials_local
    {ψ : EuN → ℝ} (y : EuN) :
    ‖fderiv ℝ ψ y‖ =
      ‖(WithLp.toLp 2
        (fun i : Fin n =>
          (fderiv ℝ ψ y) (EuclideanSpace.single i 1)) : EuN)‖ := by
  classical
  set v : EuN :=
    (InnerProductSpace.toDual ℝ EuN).symm (fderiv ℝ ψ y) with hv_def
  have hv_map : (InnerProductSpace.toDual ℝ EuN) v = fderiv ℝ ψ y := by simp [v]
  have h_fderiv_norm_eq_v : ‖fderiv ℝ ψ y‖ = ‖v‖ := by simp [v]
  have h_v_eq_components : v =
      WithLp.toLp 2
        (fun i : Fin n =>
          (fderiv ℝ ψ y) (EuclideanSpace.single i 1)) := by
    ext i
    calc
      v i = inner ℝ v (EuclideanSpace.single i (1 : ℝ)) := by
        simpa using
          (EuclideanSpace.inner_single_right (i := i) (a := (1 : ℝ)) v).symm
      _ = ((InnerProductSpace.toDual ℝ EuN) v) (EuclideanSpace.single i (1 : ℝ)) := by
        rw [InnerProductSpace.toDual_apply_apply]
      _ = (fderiv ℝ ψ y) (EuclideanSpace.single i (1 : ℝ)) := by rw [hv_map]
      _ = (WithLp.toLp 2
            (fun j : Fin n =>
              (fderiv ℝ ψ y) (EuclideanSpace.single j 1))) i := by simp
  rw [h_fderiv_norm_eq_v, h_v_eq_components]

omit [NeZero n] in
private lemma norm_fderiv_le_sum_partials_local
    (ψ : EuN → ℝ) (y : EuN) :
    ‖fderiv ℝ ψ y‖ ≤
      ∑ i : Fin n, ‖(fderiv ℝ ψ y) (EuclideanSpace.single i 1)‖ := by
  rw [norm_fderiv_eq_norm_partials_local (n := n) y]
  refine (euN_norm_le_sum_components_norms _).trans ?_
  apply le_of_eq
  refine Finset.sum_congr rfl ?_
  intro i _
  simp

omit [NeZero n] in
private lemma eLpNorm_norm_fderiv_le_sum_eLpNorm_partials
    {q : ℝ≥0∞} (hq_one : 1 ≤ q) {μ : Measure EuN}
    {f : EuN → ℝ} (hf_smooth : ContDiff ℝ (⊤ : ℕ∞) f) :
    eLpNorm (fun z : EuN => ‖fderiv ℝ f z‖) q μ ≤
      ∑ i : Fin n,
        eLpNorm (fun z : EuN => (fderiv ℝ f z) (EuclideanSpace.single i 1)) q μ := by
  classical
  have h_aesm_comp : ∀ i : Fin n,
      AEStronglyMeasurable
        (fun z : EuN => (fderiv ℝ f z) (EuclideanSpace.single i 1)) μ := by
    intro i
    have h_cont : Continuous
        (fun z : EuN => (fderiv ℝ f z) (EuclideanSpace.single i 1)) :=
      ((hf_smooth.continuous_fderiv (by simp)).clm_apply continuous_const)
    exact h_cont.aestronglyMeasurable
  have h_pt : ∀ z : EuN,
      ‖fderiv ℝ f z‖ ≤ ∑ i : Fin n,
        ‖(fderiv ℝ f z) (EuclideanSpace.single i 1)‖ :=
    fun z => norm_fderiv_le_sum_partials_local f z
  have h_step1 : eLpNorm (fun z : EuN => ‖fderiv ℝ f z‖) q μ ≤
      eLpNorm (fun z : EuN =>
        ∑ i : Fin n,
          ‖(fderiv ℝ f z) (EuclideanSpace.single i 1)‖) q μ := by
    apply eLpNorm_mono_real
    intro z
    have hh := h_pt z
    have h_norm : ‖‖fderiv ℝ f z‖‖ = ‖fderiv ℝ f z‖ :=
      Real.norm_of_nonneg (norm_nonneg _)
    rw [h_norm]
    exact hh
  refine h_step1.trans ?_
  have h_sum_le := eLpNorm_sum_le (μ := μ) (p := q)
    (s := (Finset.univ : Finset (Fin n)))
    (f := fun i => fun z : EuN => ‖(fderiv ℝ f z) (EuclideanSpace.single i 1)‖)
    (fun i _ => (h_aesm_comp i).norm) hq_one
  have h_lhs_eq :
      (fun z : EuN =>
        ∑ i : Fin n,
          ‖(fderiv ℝ f z) (EuclideanSpace.single i 1)‖) =
        ∑ i : Fin n,
          fun z : EuN => ‖(fderiv ℝ f z) (EuclideanSpace.single i 1)‖ := by
    funext z
    simp [Finset.sum_apply]
  rw [h_lhs_eq]
  refine h_sum_le.trans ?_
  apply Finset.sum_le_sum
  intro i _
  rw [eLpNorm_norm]

omit [NeZero n] in
private lemma classical_partial_ae_eq_chosenWeakPartial_local
    {q : ℝ≥0∞} (hq_one : 1 ≤ q) {Ω : Set EuN} (hΩ_open : IsOpen Ω)
    {f : EuN → ℝ} (hf_smooth : ContDiff ℝ (⊤ : ℕ∞) f)
    (hf_compact : HasCompactSupport f) (hf_supp : tsupport f ⊆ Ω)
    (i : Fin n) :
    (fun z : EuN => (fderiv ℝ f z) (EuclideanSpace.single i 1))
      =ᵐ[volume.restrict Ω]
      DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial' q i f Ω := by
  classical
  have hf_mem : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := n) 1 q f Ω :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_of_smooth_compactSupport_pub
      (d := n) hΩ_open hf_smooth hf_compact hf_supp hq_one 1
  have hf_W1p : DeGiorgi.MemW1p (d := n) q f Ω :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.one_iff_memW1p.mp hf_mem
  have h_classical_isWeak :
      DeGiorgi.HasWeakPartialDeriv (d := n) i
        (fun z : EuN => (fderiv ℝ f z) (EuclideanSpace.single i 1)) f Ω :=
    DeGiorgi.HasWeakPartialDeriv.of_contDiff (Ω := Ω) (i := i) (f := f)
      hΩ_open (hf_smooth.of_le (by norm_cast))
  have h_chosen_isWeak :
      DeGiorgi.HasWeakPartialDeriv (d := n) i
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial' q i f Ω) f Ω :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_isWeakPartial_of_mem
      hf_W1p i
  have h_classical_loc : LocallyIntegrable
      (fun z : EuN => (fderiv ℝ f z) (EuclideanSpace.single i 1))
      (volume.restrict Ω) := by
    have h_cont : Continuous
        (fun z : EuN => (fderiv ℝ f z) (EuclideanSpace.single i 1)) :=
      ((hf_smooth.continuous_fderiv (by simp)).clm_apply continuous_const)
    exact h_cont.locallyIntegrable.mono_measure Measure.restrict_le_self
  have h_chosen_loc : LocallyIntegrable
      (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial' q i f Ω)
      (volume.restrict Ω) :=
    (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_memLp_of_mem
      hf_W1p i).locallyIntegrable hq_one
  exact DeGiorgi.HasWeakPartialDeriv.ae_eq (Ω := Ω) hΩ_open
    h_classical_isWeak h_chosen_isWeak h_classical_loc h_chosen_loc

private lemma eLpNorm_norm_fderiv_le_n_mul_wkpNorm
    {q : ℝ≥0∞} (hq_one : 1 ≤ q) {Ω : Set EuN} (hΩ_open : IsOpen Ω)
    {f : EuN → ℝ} (hf_smooth : ContDiff ℝ (⊤ : ℕ∞) f)
    (hf_compact : HasCompactSupport f) (hf_supp : tsupport f ⊆ Ω) :
    eLpNorm (fun z : EuN => ‖fderiv ℝ f z‖) q (volume.restrict Ω) ≤
      ((n : ℕ) : ℝ≥0∞) *
        DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := n) 1 q f Ω := by
  classical
  have h_grad_le := eLpNorm_norm_fderiv_le_sum_eLpNorm_partials
    (q := q) hq_one (μ := volume.restrict Ω) hf_smooth
  refine h_grad_le.trans ?_
  have h_each_eq : ∀ i : Fin n,
      eLpNorm (fun z : EuN => (fderiv ℝ f z) (EuclideanSpace.single i 1)) q
        (volume.restrict Ω) =
      eLpNorm
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial' q i f Ω)
        q (volume.restrict Ω) := fun i =>
    eLpNorm_congr_ae (classical_partial_ae_eq_chosenWeakPartial_local
      hq_one hΩ_open hf_smooth hf_compact hf_supp i)
  have h_step1 :
      ∑ i : Fin n,
        eLpNorm (fun z : EuN => (fderiv ℝ f z) (EuclideanSpace.single i 1)) q
          (volume.restrict Ω)
        = ∑ i : Fin n,
          eLpNorm
            (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial' q i f Ω)
            q (volume.restrict Ω) :=
    Finset.sum_congr rfl (fun i _ => h_each_eq i)
  rw [h_step1]
  have hWkpEq :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := n) 1 q f Ω =
        ∑ j ∈ Finset.range 2,
          ∑ β : Fin j → Fin n,
            eLpNorm
              (DifferentialGeometry.Analysis.Sobolev.Euclidean.iterWeakPartial
                (d := n) q j β f Ω)
              q (volume.restrict Ω) :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_eq_sum 1 q f Ω
  have h_j1_term :
      (∑ β : Fin 1 → Fin n,
          eLpNorm
            (DifferentialGeometry.Analysis.Sobolev.Euclidean.iterWeakPartial
              (d := n) q 1 β f Ω) q (volume.restrict Ω)) =
        ∑ i : Fin n,
          eLpNorm
            (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial' q i f Ω)
            q (volume.restrict Ω) := by
    have h_unfold : ∀ β : Fin 1 → Fin n,
        eLpNorm
          (DifferentialGeometry.Analysis.Sobolev.Euclidean.iterWeakPartial
            (d := n) q 1 β f Ω) q (volume.restrict Ω) =
          eLpNorm
            (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial' q (β 0) f Ω)
            q (volume.restrict Ω) := by
      intro β
      have hit :
          DifferentialGeometry.Analysis.Sobolev.Euclidean.iterWeakPartial
              (d := n) q 1 β f Ω =
            DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial' q (β 0) f Ω := by
        rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.iterWeakPartial_succ]
        simp [DifferentialGeometry.Analysis.Sobolev.Euclidean.iterWeakPartial_zero]
      rw [hit]
    rw [Finset.sum_congr rfl (fun β _ => h_unfold β)]
    let e : (Fin 1 → Fin n) ≃ Fin n :=
      { toFun := fun β => β 0
        invFun := fun i _ => i
        left_inv := fun β => by
          funext j
          have hj : j = 0 := Subsingleton.elim _ _
          rw [hj]
        right_inv := fun _ => rfl }
    exact Fintype.sum_equiv e
      (fun β =>
        eLpNorm
          (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial' q (β 0) f Ω)
          q (volume.restrict Ω))
      (fun i =>
        eLpNorm
          (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial' q i f Ω)
          q (volume.restrict Ω))
      (fun _ => rfl)
  have h_le_wkp :
      (∑ i : Fin n,
          eLpNorm
            (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial' q i f Ω)
            q (volume.restrict Ω)) ≤
        DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := n) 1 q f Ω := by
    rw [hWkpEq, Finset.sum_range_succ, Finset.sum_range_one, ← h_j1_term]
    refine le_add_of_nonneg_left ?_
    exact zero_le _
  refine h_le_wkp.trans ?_
  have hd_pos : 0 < n := NeZero.pos _
  have hd_one_le : (1 : ℝ≥0∞) ≤ ((n : ℕ) : ℝ≥0∞) := by
    exact_mod_cast hd_pos
  conv_lhs => rw [show DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
    (d := n) 1 q f Ω = 1 *
    DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
      (d := n) 1 q f Ω from
    (one_mul _).symm]
  gcongr

private lemma eLpNorm_norm_fderiv_chartSmoothExt_pou_mul_interior_le_wkpNormHalfSpace
    {q : ℝ≥0∞} (hq_one : 1 ≤ q) {u : M → ℝ} (hu : ContMDiff I_hs 𝓘(ℝ, ℝ) ∞ u)
    (h_int : AllChartsInteriorSupport (n := n) (M := M) u) (α : M) :
    eLpNorm (fun z : EuN => ‖fderiv ℝ (chartSmoothExt (n := n) (M := M) α
        (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
          : C^∞⟮I_hs, M; ℝ⟯) x * u x)) z‖) q
      (volume.restrict
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
          (chartTargetEuclid (n := n) (M := M) α))) ≤
      ((n : ℕ) : ℝ≥0∞) *
        DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := n) 1 q
          (chartSmoothExt (n := n) (M := M) α
            (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
              : C^∞⟮I_hs, M; ℝ⟯) x * u x))
          (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
            (chartTargetEuclid (n := n) (M := M) α)) := by
  classical
  set f : EuN → ℝ := chartSmoothExt (n := n) (M := M) α
    (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
      : C^∞⟮I_hs, M; ℝ⟯) x * u x) with hf_def
  set Ω : Set EuN := DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
    (chartTargetEuclid (n := n) (M := M) α) with hΩ_def
  have hΩ_open : IsOpen Ω :=
    interiorHalfSpace_chartTargetEuclid_isOpen (n := n) (M := M) α
  have hf_smooth : ContDiff ℝ ∞ f := by
    rw [hf_def]
    exact contDiff_chartSmoothExt_pou_mul (n := n) (M := M) α
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M)
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I_hs M)
      hu (h_int α)
  have hf_smooth_top : ContDiff ℝ (⊤ : ℕ∞) f := hf_smooth
  have hf_compact : HasCompactSupport f := by
    rw [hf_def]
    exact hasCompactSupport_chartSmoothExt_pou_mul (n := n) (M := M) α
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M)
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I_hs M) u
  have hf_supp : tsupport f ⊆ Ω := by
    rw [hf_def, hΩ_def]
    set ff : M → ℝ := fun x : M =>
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
        : C^∞⟮I_hs, M; ℝ⟯) x * u x with hff_def
    have hff_supp_chart_src : tsupport ff ⊆ (chartAt (EuclideanHalfSpace n) α).source :=
      tsupport_pou_mul_subset_chart_source (n := n) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I_hs M)
        α u
    have hint_image : (extChartAt I_hs α) '' (tsupport ff) ⊆
        DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
          (chartTargetEuclid (n := n) (M := M) α) :=
      chartSmoothExtInteriorSupport_image_subset_interior
        (n := n) (M := M) (α := α) (f := ff) hff_supp_chart_src (h_int α)
    have h1 : tsupport (chartSmoothExt (n := n) (M := M) α ff) ⊆
        (extChartAt I_hs α) '' (tsupport ff) :=
      tsupport_chartSmoothExt_subset (n := n) (M := M) α hff_supp_chart_src
    exact h1.trans hint_image
  exact eLpNorm_norm_fderiv_le_n_mul_wkpNorm hq_one hΩ_open hf_smooth_top hf_compact hf_supp

omit [CompactSpace M] in
private lemma wkpNorm_chartSmoothExt_interior_eq_wkpNorm_chartPushed_interior
    {q : ℝ≥0∞} (hq_one : 1 ≤ q) (α : M) (u : M → ℝ) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := n) 1 q
        (chartSmoothExt (n := n) (M := M) α
          (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
            : C^∞⟮I_hs, M; ℝ⟯) x * u x))
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
          (chartTargetEuclid (n := n) (M := M) α)) =
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := n) 1 q
        (chartPushed (n := n) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M) α u)
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
          (chartTargetEuclid (n := n) (M := M) α)) :=
  DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_congr_ae
    (d := n) hq_one
    (interiorHalfSpace_chartTargetEuclid_isOpen (n := n) (M := M) α)
    (chartSmoothExt_ae_eq_chartPushed_interior (n := n) (M := M) α u)

omit [CompactSpace M] in
private lemma wkpNormHalfSpace_chartPushed_target_le_wkpNormChart
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I_hs M)
    {q : ℝ≥0∞} (α : M) (u : M → ℝ) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace
        (d := n) 1 q
        (chartPushed (n := n) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M) α u)
        (chartTargetEuclid (n := n) (M := M) α) ≤
      wkpNormChart (n := n) (M := M) g 1 q u := by
  classical
  let _ := g
  unfold wkpNormChart
  exact ENNReal.le_tsum α

private lemma eLpNorm_norm_fderiv_chartSmoothExt_ball_le_wkpNormChart
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I_hs M)
    {q : ℝ≥0∞} (hq_one : 1 ≤ q) {u : M → ℝ} (hu : ContMDiff I_hs 𝓘(ℝ, ℝ) ∞ u)
    (h_int : AllChartsInteriorSupport (n := n) (M := M) u) (α : M) :
    eLpNorm (fun z : EuN => ‖fderiv ℝ (chartSmoothExt (n := n) (M := M) α
        (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
          : C^∞⟮I_hs, M; ℝ⟯) x * u x)) z‖) q
      (volume.restrict (Metric.ball (0 : EuN) (chartRadius (n := n) (M := M) α))) ≤
      ((n : ℕ) : ℝ≥0∞) *
        wkpNormChart (n := n) (M := M) g 1 q u := by
  classical
  rw [eLpNorm_norm_fderiv_chartSmoothExt_pou_mul_restrict_ball_eq_restrict_interior
    (n := n) (M := M) h_int α q]
  refine (eLpNorm_norm_fderiv_chartSmoothExt_pou_mul_interior_le_wkpNormHalfSpace
    (n := n) (M := M) hq_one hu h_int α).trans ?_
  rw [wkpNorm_chartSmoothExt_interior_eq_wkpNorm_chartPushed_interior
    (n := n) (M := M) hq_one α u]
  gcongr
  change DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace
        (d := n) 1 q
        (chartPushed (n := n) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M) α u)
        (chartTargetEuclid (n := n) (M := M) α) ≤
    wkpNormChart (n := n) (M := M) g 1 q u
  exact wkpNormHalfSpace_chartPushed_target_le_wkpNormChart
    (n := n) (M := M) g α u

private lemma per_chart_smooth_sup_bound
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I_hs M)
    {p : ℝ} (hp : (n : ℝ) < p) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {u : M → ℝ}, ContMDiff I_hs 𝓘(ℝ, ℝ) ∞ u →
        AllChartsInteriorSupport (n := n) (M := M) u →
        ∀ y : EuN, ‖chartSmoothExt (n := n) (M := M) α
          (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
            : C^∞⟮I_hs, M; ℝ⟯) x * u x) y‖ ≤ C *
          (wkpNormChart (n := n) (M := M) g 1 (ENNReal.ofReal p) u).toReal := by
  classical
  have hp_pos : 0 < p := lt_of_le_of_lt (Nat.cast_nonneg _) hp
  have hp_one : 1 ≤ p := by
    have hd_pos : (0 : ℝ) < (n : ℝ) := by
      exact_mod_cast NeZero.pos n
    have hd_one_le : (1 : ℝ) ≤ (n : ℝ) := by
      have : 1 ≤ n := NeZero.one_le
      exact_mod_cast this
    linarith
  have hp_enn_one : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from by simp]
    exact ENNReal.ofReal_le_ofReal hp_one
  obtain ⟨Cmorrey, hCmorrey_nn, hbound⟩ :=
    chartSmoothExt_morrey_sup_uniform (n := n) (M := M) α hp
  refine ⟨Cmorrey * (1 + (n : ℝ)), ?_, ?_⟩
  · have hd_nn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
    positivity
  · intro u hu h_int y
    have hbound_y := hbound hu h_int y
    set f : EuN → ℝ := chartSmoothExt (n := n) (M := M) α
      (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
        : C^∞⟮I_hs, M; ℝ⟯) x * u x) with hf_def
    have hLp_bd := eLpNorm_chartSmoothExt_ball_le_wkpNormChart
      (n := n) (M := M) g h_int α (ENNReal.ofReal p)
    have hgrad_bd := eLpNorm_norm_fderiv_chartSmoothExt_ball_le_wkpNormChart
      (n := n) (M := M) g hp_enn_one hu h_int α
    have hwkp_lt_top : wkpNormChart (n := n) (M := M) g 1 (ENNReal.ofReal p) u < ⊤ := by
      have h_per_α_mem : ∀ β : M,
          DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace
            (d := n) 1 (ENNReal.ofReal p)
            (chartPushed (n := n) (M := M)
              (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M) β u)
            (chartTargetEuclid (n := n) (M := M) β) := by
        intro β
        set fβ : M → ℝ := fun x : M =>
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M β
            : C^∞⟮I_hs, M; ℝ⟯) x * u x with hfβ_def
        have hfβ_supp_chart_src : tsupport fβ ⊆ (chartAt (EuclideanHalfSpace n) β).source :=
          tsupport_pou_mul_subset_chart_source (n := n) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I_hs M)
            β u
        have hint_image : (extChartAt I_hs β) '' (tsupport fβ) ⊆
            DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
              (chartTargetEuclid (n := n) (M := M) β) :=
          chartSmoothExtInteriorSupport_image_subset_interior
            (n := n) (M := M) (α := β) (f := fβ) hfβ_supp_chart_src (h_int β)
        set ext_β : EuN → ℝ := chartSmoothExt (n := n) (M := M) β fβ with hext_β_def
        have hext_β_smooth : ContDiff ℝ ∞ ext_β := by
          rw [hext_β_def]
          exact contDiff_chartSmoothExt_pou_mul (n := n) (M := M) β
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I_hs M)
            hu (h_int β)
        have hext_β_compact : HasCompactSupport ext_β := by
          rw [hext_β_def]
          exact hasCompactSupport_chartSmoothExt_pou_mul (n := n) (M := M) β
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I_hs M) u
        have hext_β_supp : tsupport ext_β ⊆
            DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
              (chartTargetEuclid (n := n) (M := M) β) := by
          have h1 : tsupport ext_β ⊆ (extChartAt I_hs β) '' (tsupport fβ) := by
            rw [hext_β_def]
            exact tsupport_chartSmoothExt_subset (n := n) (M := M) β hfβ_supp_chart_src
          exact h1.trans hint_image
        have hOpen_int : IsOpen (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
            (chartTargetEuclid (n := n) (M := M) β)) :=
          interiorHalfSpace_chartTargetEuclid_isOpen (n := n) (M := M) β
        have hext_β_W1p : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
            (d := n) 1 (ENNReal.ofReal p) ext_β
            (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
              (chartTargetEuclid (n := n) (M := M) β)) :=
          DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_of_smooth_compactSupport_pub
            (d := n) hOpen_int hext_β_smooth hext_β_compact hext_β_supp hp_enn_one 1
        have h_ae : ext_β =ᵐ[volume.restrict
            (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
              (chartTargetEuclid (n := n) (M := M) β))]
            chartPushed (n := n) (M := M)
              (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M) β u := by
          rw [hext_β_def, hfβ_def]
          exact chartSmoothExt_ae_eq_chartPushed_interior (n := n) (M := M) β u
        have h_chartPushed_W1p : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
            (d := n) 1 (ENNReal.ofReal p)
            (chartPushed (n := n) (M := M)
              (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M) β u)
            (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
              (chartTargetEuclid (n := n) (M := M) β)) :=
          (DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_congr_ae
            (d := n) hp_enn_one hOpen_int h_ae).mp hext_β_W1p
        exact h_chartPushed_W1p
      have h_mem_chart : MemWkpChart (n := n) (M := M) g 1 (ENNReal.ofReal p) u :=
        h_per_α_mem
      exact wkpNormChart_lt_top_of_memWkpChart (n := n) (M := M) g hp_enn_one h_mem_chart
    have hwkp_ne_top : wkpNormChart (n := n) (M := M) g 1 (ENNReal.ofReal p) u ≠ ⊤ :=
      hwkp_lt_top.ne
    set N : ℝ := (wkpNormChart (n := n) (M := M) g 1 (ENNReal.ofReal p) u).toReal with hN_def
    have hN_nn : 0 ≤ N := ENNReal.toReal_nonneg
    have hLp_real : (eLpNorm f (ENNReal.ofReal p)
        (volume.restrict (Metric.ball (0 : EuN) (chartRadius (n := n) (M := M) α)))).toReal
        ≤ N := by
      apply ENNReal.toReal_mono hwkp_ne_top
      exact hLp_bd
    have hgrad_real : (eLpNorm (fun z : EuN => ‖fderiv ℝ f z‖) (ENNReal.ofReal p)
        (volume.restrict (Metric.ball (0 : EuN) (chartRadius (n := n) (M := M) α)))).toReal
        ≤ (n : ℝ) * N := by
      have h_ne_top : ((n : ℕ) : ℝ≥0∞) *
          wkpNormChart (n := n) (M := M) g 1 (ENNReal.ofReal p) u ≠ ⊤ :=
        ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hwkp_ne_top
      have h_le := ENNReal.toReal_mono h_ne_top hgrad_bd
      rwa [ENNReal.toReal_mul, ENNReal.toReal_natCast] at h_le
    have h_combined : (eLpNorm f (ENNReal.ofReal p)
        (volume.restrict (Metric.ball (0 : EuN) (chartRadius (n := n) (M := M) α)))).toReal +
      (eLpNorm (fun z : EuN => ‖fderiv ℝ f z‖) (ENNReal.ofReal p)
        (volume.restrict (Metric.ball (0 : EuN) (chartRadius (n := n) (M := M) α)))).toReal ≤
      N + (n : ℝ) * N := by
      linarith
    have h_final : Cmorrey * ((eLpNorm f (ENNReal.ofReal p)
        (volume.restrict (Metric.ball (0 : EuN) (chartRadius (n := n) (M := M) α)))).toReal +
      (eLpNorm (fun z : EuN => ‖fderiv ℝ f z‖) (ENNReal.ofReal p)
        (volume.restrict (Metric.ball (0 : EuN) (chartRadius (n := n) (M := M) α)))).toReal) ≤
      Cmorrey * (1 + (n : ℝ)) * N := by
      have h1 : Cmorrey * (N + (n : ℝ) * N) = Cmorrey * (1 + (n : ℝ)) * N := by ring
      calc Cmorrey * ((eLpNorm f (ENNReal.ofReal p)
          (volume.restrict (Metric.ball (0 : EuN) (chartRadius (n := n) (M := M) α)))).toReal +
        (eLpNorm (fun z : EuN => ‖fderiv ℝ f z‖) (ENNReal.ofReal p)
          (volume.restrict (Metric.ball (0 : EuN) (chartRadius (n := n) (M := M) α)))).toReal)
          ≤ Cmorrey * (N + (n : ℝ) * N) :=
            mul_le_mul_of_nonneg_left h_combined hCmorrey_nn
        _ = Cmorrey * (1 + (n : ℝ)) * N := h1
    rw [hf_def] at h_final
    exact le_trans hbound_y h_final

omit [CompactSpace M] in

private lemma chartSmoothExt_pou_mul_apply_at_chart_image
    (α : M) (u : M → ℝ) {x : M} (hx : x ∈ (chartAt (EuclideanHalfSpace n) α).source) :
    chartSmoothExt (n := n) (M := M) α
        (fun y : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
          : C^∞⟮I_hs, M; ℝ⟯) y * u y)
        (extChartAt I_hs α x) =
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
        : C^∞⟮I_hs, M; ℝ⟯) x * u x := by
  classical
  have hx_target : extChartAt I_hs α x ∈ (extChartAt I_hs α).target :=
    (extChartAt I_hs α).map_source (by
      rw [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
        (I := I_hs) (M := M)]
      exact hx)
  rw [chartSmoothExt_apply_of_mem_target (n := n) (M := M) α _ hx_target]
  rw [(extChartAt I_hs α).left_inv (by
    rw [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
      (I := I_hs) (M := M)]
    exact hx)]

omit [CompactSpace M] in
private lemma norm_pou_mul_le_norm_chartSmoothExt_at_some_point
    (α : M) (u : M → ℝ) (x : M) {Cmod : ℝ}
    (hbound : ∀ y : EuN, ‖chartSmoothExt (n := n) (M := M) α
      (fun z : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
        : C^∞⟮I_hs, M; ℝ⟯) z * u z) y‖ ≤ Cmod) (hCmod : 0 ≤ Cmod) :
    ‖(DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
      : C^∞⟮I_hs, M; ℝ⟯) x * u x‖ ≤ Cmod := by
  classical
  by_cases hx : x ∈ (chartAt (EuclideanHalfSpace n) α).source
  · have h_eq := chartSmoothExt_pou_mul_apply_at_chart_image (n := n) (M := M) α u hx
    rw [← h_eq]
    exact hbound _
  · have hρ_zero : (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
        : C^∞⟮I_hs, M; ℝ⟯) x = 0 := by
      have hsubord :
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M).IsSubordinate
            (fun α : M => (chartAt (EuclideanHalfSpace n) α).source) :=
        DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I_hs M
      have h_supp := hsubord α
      by_contra hne
      apply hx
      apply h_supp
      apply subset_tsupport
      exact Function.mem_support.mpr hne
    rw [hρ_zero, zero_mul, norm_zero]
    exact hCmod

private noncomputable def perChartMorreyConst
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I_hs M)
    {p : ℝ} (hp : (n : ℝ) < p) (α : M) : ℝ :=
  Classical.choose (per_chart_smooth_sup_bound (n := n) (M := M) g hp α)

private lemma perChartMorreyConst_nn
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I_hs M)
    {p : ℝ} (hp : (n : ℝ) < p) (α : M) :
    0 ≤ perChartMorreyConst (n := n) (M := M) g hp α :=
  (Classical.choose_spec
    (per_chart_smooth_sup_bound (n := n) (M := M) g hp α)).1

private lemma perChartMorreyConst_bound
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I_hs M)
    {p : ℝ} (hp : (n : ℝ) < p) (α : M)
    {u : M → ℝ} (hu : ContMDiff I_hs 𝓘(ℝ, ℝ) ∞ u)
    (h_int : AllChartsInteriorSupport (n := n) (M := M) u) (y : EuN) :
    ‖chartSmoothExt (n := n) (M := M) α
        (fun z : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
          : C^∞⟮I_hs, M; ℝ⟯) z * u z) y‖ ≤
      perChartMorreyConst (n := n) (M := M) g hp α *
        (wkpNormChart (n := n) (M := M) g 1 (ENNReal.ofReal p) u).toReal :=
  (Classical.choose_spec
    (per_chart_smooth_sup_bound (n := n) (M := M) g hp α)).2 hu h_int y

theorem smooth_manifold_morrey_sup_bound_uniform_withBoundary
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I_hs M)
    {p : ℝ} (hp : (n : ℝ) < p) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {u : M → ℝ}, ContMDiff I_hs 𝓘(ℝ, ℝ) ∞ u →
        AllChartsInteriorSupport (n := n) (M := M) u →
        ∀ x : M, ‖u x‖ ≤ C *
          (wkpNormChart (n := n) (M := M) g 1 (ENNReal.ofReal p) u).toReal := by
  classical
  set S : Finset M :=
    DifferentialGeometry.Integral.Measure.chartAtlasPOU_finset (I := I_hs) (M := M)
    with hS_def
  refine ⟨∑ α ∈ S, perChartMorreyConst (n := n) (M := M) g hp α, ?_, ?_⟩
  · exact Finset.sum_nonneg (fun α _ =>
      perChartMorreyConst_nn (n := n) (M := M) g hp α)
  intro u hu h_int x
  have h_decomp : u x = ∑ α ∈ S,
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α : M → ℝ) x * u x := by
    have hsum : ∑ α ∈ S,
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α : M → ℝ) x = 1 :=
      DifferentialGeometry.Analysis.Sobolev.Chart.chartAtlasPOU_finset_sum_eq_one
        (I := I_hs) (M := M) x
    rw [← Finset.sum_mul, hsum, one_mul]
  rw [h_decomp]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro α _
  have hC_α_nn : 0 ≤ perChartMorreyConst (n := n) (M := M) g hp α :=
    perChartMorreyConst_nn (n := n) (M := M) g hp α
  have hCN_nn : 0 ≤ perChartMorreyConst (n := n) (M := M) g hp α *
      (wkpNormChart (n := n) (M := M) g 1 (ENNReal.ofReal p) u).toReal :=
    mul_nonneg hC_α_nn ENNReal.toReal_nonneg
  refine norm_pou_mul_le_norm_chartSmoothExt_at_some_point
    (n := n) (M := M) α u x ?_ hCN_nn
  intro y
  exact perChartMorreyConst_bound (n := n) (M := M) g hp α hu h_int y

private lemma chartSmoothExt_holder_uniform_half_ball
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I_hs M)
    (α : M) {p : ℝ} (hp : (n : ℝ) < p) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {u : M → ℝ}, ContMDiff I_hs 𝓘(ℝ, ℝ) ∞ u →
        AllChartsInteriorSupport (n := n) (M := M) u →
        ∀ y₁ y₂ : EuN,
          y₁ ∈ Metric.ball (0 : EuN) (chartRadius (n := n) (M := M) α / 2) →
          y₂ ∈ Metric.ball (0 : EuN) (chartRadius (n := n) (M := M) α / 2) →
          ‖chartSmoothExt (n := n) (M := M) α
              (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
                : C^∞⟮I_hs, M; ℝ⟯) x * u x) y₁ -
            chartSmoothExt (n := n) (M := M) α
              (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
                : C^∞⟮I_hs, M; ℝ⟯) x * u x) y₂‖ ≤
            C * ‖y₁ - y₂‖ ^ (1 - (n : ℝ) / p) *
              (wkpNormChart (n := n) (M := M) g 1 (ENNReal.ofReal p) u).toReal := by
  classical
  have hd_pos : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast NeZero.pos n
  have hd_one_le : (1 : ℝ) ≤ (n : ℝ) := by
    have : 1 ≤ n := NeZero.one_le
    exact_mod_cast this
  have hp_pos : 0 < p := lt_of_le_of_lt hd_pos.le hp
  have hp_one : 1 ≤ p := by linarith
  have hp_enn_one : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from by simp]
    exact ENNReal.ofReal_le_ofReal hp_one
  set R : ℝ := chartRadius (n := n) (M := M) α with hR_def
  have hR_pos : 0 < R := chartRadius_pos (n := n) (M := M) α
  obtain ⟨C₀, hC₀_nn, hbound⟩ :=
    DifferentialGeometry.Analysis.Sobolev.EuclideanMorrey.smooth_morrey_pair_bound_uniform
      (d := n) hp
      (x₀ := (0 : EuN)) (R := R) hR_pos
  refine ⟨C₀ * (n : ℝ), mul_nonneg hC₀_nn (Nat.cast_nonneg _), ?_⟩
  intro u hu h_int y₁ y₂ hy₁ hy₂
  set f : EuN → ℝ := chartSmoothExt (n := n) (M := M) α
    (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
      : C^∞⟮I_hs, M; ℝ⟯) x * u x) with hf_def
  have hf_smooth_top : ContDiff ℝ (⊤ : ℕ∞) f := by
    rw [hf_def]
    exact contDiff_chartSmoothExt_pou_mul (n := n) (M := M) α
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M)
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I_hs M)
      hu (h_int α)
  have h_pair := hbound (u := f) hf_smooth_top hy₁ hy₂
  have h_grad_bd := eLpNorm_norm_fderiv_chartSmoothExt_ball_le_wkpNormChart
    (n := n) (M := M) g (q := ENNReal.ofReal p) hp_enn_one hu h_int α
  have hwkp_lt_top : wkpNormChart (n := n) (M := M) g 1 (ENNReal.ofReal p) u < ⊤ := by
    have h_per_α_mem : ∀ β : M,
        DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace
          (d := n) 1 (ENNReal.ofReal p)
          (chartPushed (n := n) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M) β u)
          (chartTargetEuclid (n := n) (M := M) β) := by
      intro β
      set fβ : M → ℝ := fun x : M =>
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M β
          : C^∞⟮I_hs, M; ℝ⟯) x * u x with hfβ_def
      have hfβ_supp_chart_src : tsupport fβ ⊆ (chartAt (EuclideanHalfSpace n) β).source :=
        tsupport_pou_mul_subset_chart_source (n := n) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I_hs M)
          β u
      have hint_image : (extChartAt I_hs β) '' (tsupport fβ) ⊆
          DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
            (chartTargetEuclid (n := n) (M := M) β) :=
        chartSmoothExtInteriorSupport_image_subset_interior
          (n := n) (M := M) (α := β) (f := fβ) hfβ_supp_chart_src (h_int β)
      set ext_β : EuN → ℝ := chartSmoothExt (n := n) (M := M) β fβ with hext_β_def
      have hext_β_smooth : ContDiff ℝ ∞ ext_β := by
        rw [hext_β_def]
        exact contDiff_chartSmoothExt_pou_mul (n := n) (M := M) β
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I_hs M)
          hu (h_int β)
      have hext_β_compact : HasCompactSupport ext_β := by
        rw [hext_β_def]
        exact hasCompactSupport_chartSmoothExt_pou_mul (n := n) (M := M) β
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I_hs M) u
      have hext_β_supp : tsupport ext_β ⊆
          DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
            (chartTargetEuclid (n := n) (M := M) β) := by
        have h1 : tsupport ext_β ⊆ (extChartAt I_hs β) '' (tsupport fβ) := by
          rw [hext_β_def]
          exact tsupport_chartSmoothExt_subset (n := n) (M := M) β hfβ_supp_chart_src
        exact h1.trans hint_image
      have hOpen_int : IsOpen (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
          (chartTargetEuclid (n := n) (M := M) β)) :=
        interiorHalfSpace_chartTargetEuclid_isOpen (n := n) (M := M) β
      have hext_β_W1p : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
          (d := n) 1 (ENNReal.ofReal p) ext_β
          (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
            (chartTargetEuclid (n := n) (M := M) β)) :=
        DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_of_smooth_compactSupport_pub
          (d := n) hOpen_int hext_β_smooth hext_β_compact hext_β_supp hp_enn_one 1
      have h_ae : ext_β =ᵐ[volume.restrict
          (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
            (chartTargetEuclid (n := n) (M := M) β))]
          chartPushed (n := n) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M) β u := by
        rw [hext_β_def, hfβ_def]
        exact chartSmoothExt_ae_eq_chartPushed_interior (n := n) (M := M) β u
      exact (DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_congr_ae
        (d := n) hp_enn_one hOpen_int h_ae).mp hext_β_W1p
    exact wkpNormChart_lt_top_of_memWkpChart (n := n) (M := M) g hp_enn_one h_per_α_mem
  have hwkp_ne_top : wkpNormChart (n := n) (M := M) g 1 (ENNReal.ofReal p) u ≠ ⊤ :=
    hwkp_lt_top.ne
  set N : ℝ := (wkpNormChart (n := n) (M := M) g 1 (ENNReal.ofReal p) u).toReal with hN_def
  have hN_nn : 0 ≤ N := ENNReal.toReal_nonneg
  have h_d_wkp_ne_top : ((n : ℕ) : ℝ≥0∞) *
      wkpNormChart (n := n) (M := M) g 1 (ENNReal.ofReal p) u ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hwkp_ne_top
  have h_grad_real :
      (eLpNorm (fun z : EuN => ‖fderiv ℝ f z‖) (ENNReal.ofReal p)
        (volume.restrict (Metric.ball (0 : EuN) R))).toReal ≤
        (n : ℝ) * N := by
    have h_le := ENNReal.toReal_mono h_d_wkp_ne_top h_grad_bd
    rw [ENNReal.toReal_mul, ENNReal.toReal_natCast] at h_le
    exact h_le
  have h_dist_eq : dist y₁ y₂ = ‖y₁ - y₂‖ := dist_eq_norm y₁ y₂
  have h_dist_pow_nn : 0 ≤ dist y₁ y₂ ^ (1 - (n : ℝ) / p) :=
    Real.rpow_nonneg dist_nonneg _
  calc ‖f y₁ - f y₂‖
      ≤ C₀ * dist y₁ y₂ ^ (1 - (n : ℝ) / p) *
          (eLpNorm (fun z : EuN => ‖fderiv ℝ f z‖) (ENNReal.ofReal p)
            (volume.restrict (Metric.ball (0 : EuN) R))).toReal := h_pair
    _ ≤ C₀ * dist y₁ y₂ ^ (1 - (n : ℝ) / p) * ((n : ℝ) * N) := by
        apply mul_le_mul_of_nonneg_left h_grad_real
        exact mul_nonneg hC₀_nn h_dist_pow_nn
    _ = C₀ * (n : ℝ) * ‖y₁ - y₂‖ ^ (1 - (n : ℝ) / p) * N := by
        rw [h_dist_eq]; ring

private lemma extChartAt_mem_half_ball_of_mem_tsupport_pou
    (α : M) {x : M}
    (hx : x ∈ tsupport ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
      : C^∞⟮I_hs, M; ℝ⟯) : M → ℝ)) :
    extChartAt I_hs α x ∈
      Metric.ball (0 : EuN) (chartRadius (n := n) (M := M) α / 2) := by
  classical
  have h_in : extChartAt I_hs α x ∈ chartCarrier (n := n) (M := M) α :=
    ⟨x, hx, rfl⟩
  exact chartCarrier_subset_half_ball (n := n) (M := M) α h_in

private lemma pou_mul_holder_chart_uniform_tsupport
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I_hs M)
    (α : M) {p : ℝ} (hp : (n : ℝ) < p) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {u : M → ℝ}, ContMDiff I_hs 𝓘(ℝ, ℝ) ∞ u →
        AllChartsInteriorSupport (n := n) (M := M) u →
        ∀ x ∈ tsupport ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
          : C^∞⟮I_hs, M; ℝ⟯) : M → ℝ),
        ∀ y ∈ tsupport ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
          : C^∞⟮I_hs, M; ℝ⟯) : M → ℝ),
          ‖(DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
              : C^∞⟮I_hs, M; ℝ⟯) x * u x -
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
              : C^∞⟮I_hs, M; ℝ⟯) y * u y‖ ≤
            C * ‖(extChartAt I_hs α x) - (extChartAt I_hs α y)‖ ^
                (1 - (n : ℝ) / p) *
              (wkpNormChart (n := n) (M := M) g 1 (ENNReal.ofReal p) u).toReal := by
  classical
  obtain ⟨C, hC_nn, hbound⟩ :=
    chartSmoothExt_holder_uniform_half_ball (n := n) (M := M) g α hp
  refine ⟨C, hC_nn, ?_⟩
  intro u hu h_int x hx y hy
  have h_subord :
      tsupport ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
        : C^∞⟮I_hs, M; ℝ⟯) : M → ℝ) ⊆ (chartAt (EuclideanHalfSpace n) α).source :=
    DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I_hs M α
  have hx_src : x ∈ (chartAt (EuclideanHalfSpace n) α).source := h_subord hx
  have hy_src : y ∈ (chartAt (EuclideanHalfSpace n) α).source := h_subord hy
  set y₁ : EuN := extChartAt I_hs α x with hy₁_def
  set y₂ : EuN := extChartAt I_hs α y with hy₂_def
  have hy₁_R2 : y₁ ∈ Metric.ball (0 : EuN)
      (chartRadius (n := n) (M := M) α / 2) :=
    extChartAt_mem_half_ball_of_mem_tsupport_pou (n := n) (M := M) α hx
  have hy₂_R2 : y₂ ∈ Metric.ball (0 : EuN)
      (chartRadius (n := n) (M := M) α / 2) :=
    extChartAt_mem_half_ball_of_mem_tsupport_pou (n := n) (M := M) α hy
  have h_pair := hbound hu h_int y₁ y₂ hy₁_R2 hy₂_R2
  have h_eq_x :
      chartSmoothExt (n := n) (M := M) α
          (fun z : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
            : C^∞⟮I_hs, M; ℝ⟯) z * u z) y₁ =
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
          : C^∞⟮I_hs, M; ℝ⟯) x * u x := by
    rw [hy₁_def]
    exact chartSmoothExt_pou_mul_apply_at_chart_image (n := n) (M := M) α u hx_src
  have h_eq_y :
      chartSmoothExt (n := n) (M := M) α
          (fun z : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
            : C^∞⟮I_hs, M; ℝ⟯) z * u z) y₂ =
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
          : C^∞⟮I_hs, M; ℝ⟯) y * u y := by
    rw [hy₂_def]
    exact chartSmoothExt_pou_mul_apply_at_chart_image (n := n) (M := M) α u hy_src
  rw [h_eq_x, h_eq_y] at h_pair
  exact h_pair

theorem smooth_manifold_morrey_holder_modulus_per_chart_withBoundary
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I_hs M)
    {p : ℝ} (hp : (n : ℝ) < p) (α : M) :
    ∃ K : Set M, IsCompact K ∧ K ⊆ (chartAt (EuclideanHalfSpace n) α).source ∧
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {u : M → ℝ}, ContMDiff I_hs 𝓘(ℝ, ℝ) ∞ u →
        AllChartsInteriorSupport (n := n) (M := M) u →
        ∀ x ∈ K, ∀ y ∈ K,
          ‖(DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
              : C^∞⟮I_hs, M; ℝ⟯) x * u x -
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
              : C^∞⟮I_hs, M; ℝ⟯) y * u y‖ ≤
            C * ‖(extChartAt I_hs α x) - (extChartAt I_hs α y)‖ ^
                (1 - (n : ℝ) / p) *
              (wkpNormChart (n := n) (M := M) g 1 (ENNReal.ofReal p) u).toReal := by
  classical
  set Tα : Set M := tsupport
    ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
      : C^∞⟮I_hs, M; ℝ⟯) : M → ℝ) with hTα_def
  refine ⟨Tα, (isClosed_tsupport _).isCompact, ?_, ?_⟩
  · exact DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I_hs M α
  · obtain ⟨C, hC_nn, hbound⟩ :=
      pou_mul_holder_chart_uniform_tsupport (n := n) (M := M) g α hp
    exact ⟨C, hC_nn, fun {u} hu h_int x hx y hy => hbound hu h_int x hx y hy⟩

theorem norm_sub_le_sum_pou_diff_withBoundary
    (u : M → ℝ) (x y : M) :
    ‖u x - u y‖ ≤
      ∑ α ∈ DifferentialGeometry.Integral.Measure.chartAtlasPOU_finset
        (I := I_hs) (M := M),
        ‖(DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
            : C^∞⟮I_hs, M; ℝ⟯) x * u x -
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
            : C^∞⟮I_hs, M; ℝ⟯) y * u y‖ := by
  classical
  set S : Finset M :=
    DifferentialGeometry.Integral.Measure.chartAtlasPOU_finset (I := I_hs) (M := M)
    with hS_def
  have hsum_x : ∑ α ∈ S,
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α : M → ℝ) x = 1 :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartAtlasPOU_finset_sum_eq_one
      (I := I_hs) (M := M) x
  have hsum_y : ∑ α ∈ S,
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α : M → ℝ) y = 1 :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartAtlasPOU_finset_sum_eq_one
      (I := I_hs) (M := M) y
  have h_diff_eq : u x - u y =
      ∑ α ∈ S,
        ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α : M → ℝ) x * u x -
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α : M → ℝ) y * u y) := by
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
        hsum_x, hsum_y, one_mul, one_mul]
  rw [h_diff_eq]
  exact norm_sum_le (E := ℝ) S (fun α =>
    (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α : M → ℝ) x * u x -
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α : M → ℝ) y * u y)

omit [T2Space M] [SigmaCompactSpace M] [CompactSpace M] in
theorem smooth_manifold_morrey_sup_bound_uniform_withBoundary_unconditional
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I_hs M)
    {p : ℝ} (hp : (n : ℝ) < p) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {u : M → ℝ}, ContMDiff I_hs 𝓘(ℝ, ℝ) ∞ u →
        AllChartsInteriorSupport (n := n) (M := M) u →
        ∀ x : M, ‖u x‖ ≤ C *
          (wkpNormChart (n := n) (M := M) g 1 (ENNReal.ofReal p) u).toReal :=
  smooth_manifold_morrey_sup_bound_uniform_withBoundary
    (n := n) (M := M) g hp

end WithBoundary
end Sobolev
end Analysis
end DifferentialGeometry
