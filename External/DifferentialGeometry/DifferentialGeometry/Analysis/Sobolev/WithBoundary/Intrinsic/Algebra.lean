import DifferentialGeometry.Analysis.Sobolev.WithBoundary.Embedding.MorreyManifold
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Multiplication.MultiplyQuant


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
  [T2Space M] [SigmaCompactSpace M]

local notation "EuN" => EuclideanSpace ℝ (Fin n)
local notation "I_hs" => modelWithCornersEuclideanHalfSpace n

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem chartPushed_mul_norm_le
    (α : M) {u v : M → ℝ} {uMax vMax : ℝ}
    (hu_bound : ∀ x : M, ‖u x‖ ≤ uMax) (hv_bound : ∀ x : M, ‖v x‖ ≤ vMax)
    (huMax_nn : 0 ≤ uMax) (y : EuN) :
    ‖chartPushed (n := n) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M) α
        (fun x => u x * v x) y‖ ≤ uMax * vMax := by
  classical
  unfold chartPushed
  set x : M := (extChartAt I_hs α).symm y with hx_def
  set ρ : ℝ := ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
    : C^∞⟮I_hs, M; ℝ⟯) : M → ℝ) x with hρ_def
  have hρ_nn : 0 ≤ ρ := by
    rw [hρ_def]
    exact (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M).nonneg α x
  have hρ_le_one : ρ ≤ 1 := by
    rw [hρ_def]
    exact (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M).le_one α x
  have h_uvx : ‖u x * v x‖ ≤ uMax * vMax := by
    rw [norm_mul]
    exact mul_le_mul (hu_bound x) (hv_bound x) (norm_nonneg _) huMax_nn
  calc ‖ρ * (u x * v x)‖
      = |ρ| * ‖u x * v x‖ := by rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
    _ = ρ * ‖u x * v x‖ := by rw [abs_of_nonneg hρ_nn]
    _ ≤ 1 * ‖u x * v x‖ := by gcongr
    _ = ‖u x * v x‖ := one_mul _
    _ ≤ uMax * vMax := h_uvx

theorem tsupport_pou_mul_uv_subset_pou_mul_u
    (α : M) (u v : M → ℝ) :
    tsupport (fun x : M => ((DifferentialGeometry.Integral.Measure.chartAtlasPOU
        I_hs M α : C^∞⟮I_hs, M; ℝ⟯) : M → ℝ) x * (u x * v x)) ⊆
      tsupport (fun x : M => ((DifferentialGeometry.Integral.Measure.chartAtlasPOU
        I_hs M α : C^∞⟮I_hs, M; ℝ⟯) : M → ℝ) x * u x) := by
  classical
  set ρ : M → ℝ := fun x : M => ((DifferentialGeometry.Integral.Measure.chartAtlasPOU
    I_hs M α : C^∞⟮I_hs, M; ℝ⟯) : M → ℝ) x with hρ_def
  have h_supp_sub : Function.support (fun x : M => ρ x * (u x * v x)) ⊆
      Function.support (fun x : M => ρ x * u x) := by
    intro x hx
    rw [Function.mem_support] at hx
    rw [Function.mem_support]
    intro h_eq
    apply hx
    rw [show (ρ x * (u x * v x) : ℝ) = (ρ x * u x) * v x from by ring, h_eq, zero_mul]
  exact closure_mono h_supp_sub

theorem chart_image_tsupport_pou_mul_uv_subset
    (α : M) (u v : M → ℝ) :
    (extChartAt I_hs α) '' (tsupport (fun x : M =>
      ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
          : C^∞⟮I_hs, M; ℝ⟯) : M → ℝ) x * (u x * v x))) ⊆
    (extChartAt I_hs α) '' (tsupport (fun x : M =>
      ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
          : C^∞⟮I_hs, M; ℝ⟯) : M → ℝ) x * u x)) :=
  Set.image_mono (tsupport_pou_mul_uv_subset_pou_mul_u (n := n) (M := M) α u v)

theorem AllChartsInteriorSupport.mul_left
    {u : M → ℝ} (v : M → ℝ)
    (hu : AllChartsInteriorSupport (n := n) (M := M) u) :
    AllChartsInteriorSupport (n := n) (M := M) (fun x => u x * v x) := by
  classical
  intro α
  unfold chartSmoothExtInteriorSupport
  refine (chart_image_tsupport_pou_mul_uv_subset (n := n) (M := M) α u v).trans ?_
  exact hu α

theorem AllChartsInteriorSupport.mul_right
    (u : M → ℝ) {v : M → ℝ}
    (hv : AllChartsInteriorSupport (n := n) (M := M) v) :
    AllChartsInteriorSupport (n := n) (M := M) (fun x => u x * v x) := by
  classical
  have h_comm : (fun x : M => u x * v x) = (fun x : M => v x * u x) := by
    funext x; ring
  rw [h_comm]
  exact AllChartsInteriorSupport.mul_left (n := n) (M := M) u hv

theorem AllChartsInteriorSupport.mul
    {u v : M → ℝ}
    (hu : AllChartsInteriorSupport (n := n) (M := M) u)
    (_hv : AllChartsInteriorSupport (n := n) (M := M) v) :
    AllChartsInteriorSupport (n := n) (M := M) (fun x => u x * v x) :=
  AllChartsInteriorSupport.mul_left (n := n) (M := M) v hu

theorem chartPushed_mul_norm_le_uMax_chartPushed
    (α : M) {u v : M → ℝ} {uMax : ℝ}
    (hu_bound : ∀ x : M, ‖u x‖ ≤ uMax) (_huMax_nn : 0 ≤ uMax) (y : EuN) :
    ‖chartPushed (n := n) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M) α
        (fun x => u x * v x) y‖ ≤
      uMax * ‖chartPushed (n := n) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M) α v y‖ := by
  classical
  unfold chartPushed
  set x : M := (extChartAt I_hs α).symm y with hx_def
  set ρ : ℝ := ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
    : C^∞⟮I_hs, M; ℝ⟯) : M → ℝ) x with hρ_def
  have h_norm_uv : ‖ρ * (u x * v x)‖ = ‖ρ‖ * ‖u x‖ * ‖v x‖ := by
    rw [norm_mul, norm_mul]; ring
  have h_norm_v : ‖ρ * v x‖ = ‖ρ‖ * ‖v x‖ := norm_mul _ _
  rw [h_norm_uv, h_norm_v]
  calc ‖ρ‖ * ‖u x‖ * ‖v x‖
      = (‖ρ‖ * ‖v x‖) * ‖u x‖ := by ring
    _ ≤ (‖ρ‖ * ‖v x‖) * uMax := by
        apply mul_le_mul_of_nonneg_left (hu_bound x)
        exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
    _ = uMax * (‖ρ‖ * ‖v x‖) := by ring

theorem eLpNorm_chartPushed_mul_le_uMax_mul
    (α : M) {u v : M → ℝ} {uMax : ℝ}
    (hu_bound : ∀ x : M, ‖u x‖ ≤ uMax) (huMax_nn : 0 ≤ uMax)
    (q : ℝ≥0∞) (μ : Measure EuN) :
    eLpNorm (chartPushed (n := n) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M) α
        (fun x => u x * v x)) q μ ≤
      ENNReal.ofReal uMax *
        eLpNorm (chartPushed (n := n) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M) α v) q μ := by
  refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul (g := chartPushed (n := n) (M := M)
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M) α v)
    (c := uMax) ?_ q
  refine Filter.Eventually.of_forall (fun y => ?_)
  exact chartPushed_mul_norm_le_uMax_chartPushed (n := n) (M := M) α hu_bound huMax_nn y

theorem wkpNormHalfSpace_zero_chartPushed_mul_le
    (α : M) {u v : M → ℝ} {uMax : ℝ}
    (hu_bound : ∀ x : M, ‖u x‖ ≤ uMax) (huMax_nn : 0 ≤ uMax)
    (p : ℝ≥0∞) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace
        (d := n) 0 p
        (chartPushed (n := n) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M) α
          (fun x => u x * v x))
        (chartTargetEuclid (n := n) (M := M) α) ≤
      ENNReal.ofReal uMax *
        DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace
          (d := n) 0 p
          (chartPushed (n := n) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M) α v)
          (chartTargetEuclid (n := n) (M := M) α) := by
  rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace_zero
        (d := n) p _ _,
      DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace_zero
        (d := n) p _ _]
  exact eLpNorm_chartPushed_mul_le_uMax_mul (n := n) (M := M) α hu_bound huMax_nn p _

theorem wkpNormChart_zero_mul_le_const_mul_wkpNormChart_withBoundary
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I_hs M)
    {u v : M → ℝ} {uMax : ℝ}
    (hu_bound : ∀ x : M, ‖u x‖ ≤ uMax) (huMax_nn : 0 ≤ uMax) (p : ℝ≥0∞) :
    wkpNormChart (n := n) (M := M) g 0 p (fun x => u x * v x) ≤
      ENNReal.ofReal uMax *
        wkpNormChart (n := n) (M := M) g 0 p v := by
  classical
  unfold wkpNormChart
  rw [← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum (fun α => ?_)
  exact wkpNormHalfSpace_zero_chartPushed_mul_le (n := n) (M := M) α hu_bound huMax_nn p

private noncomputable def chartPullbackZeroExtend (α : M) (f : M → ℝ) :
    EuclideanSpace ℝ (Fin n) → ℝ := by
  classical
  exact fun y =>
    if y ∈ (extChartAt I_hs α).target then
      f ((extChartAt I_hs α).symm y)
    else 0

omit [IsManifold (𝓡∂ n) ∞ M] [T2Space M] [SigmaCompactSpace M] in
private lemma chartSmoothExt_local_apply_of_mem_target
    (α : M) (f : M → ℝ) {y : EuclideanSpace ℝ (Fin n)}
    (hy : y ∈ (extChartAt I_hs α).target) :
    chartPullbackZeroExtend (n := n) (M := M) α f y =
      f ((extChartAt I_hs α).symm y) := by
  classical
  change (if y ∈ (extChartAt I_hs α).target then
      f ((extChartAt I_hs α).symm y)
    else 0) = f ((extChartAt I_hs α).symm y)
  rw [if_pos hy]

omit [IsManifold (𝓡∂ n) ∞ M] [T2Space M] [SigmaCompactSpace M] in
private lemma chartSmoothExt_local_apply_of_notMem_target
    (α : M) (f : M → ℝ) {y : EuclideanSpace ℝ (Fin n)}
    (hy : y ∉ (extChartAt I_hs α).target) :
    chartPullbackZeroExtend (n := n) (M := M) α f y = 0 := by
  classical
  change (if y ∈ (extChartAt I_hs α).target then
      f ((extChartAt I_hs α).symm y)
    else 0) = 0
  rw [if_neg hy]

private lemma chartSmoothExt_local_eq_chartPushed_on_target
    (α : M) (u : M → ℝ) {y : EuclideanSpace ℝ (Fin n)}
    (hy : y ∈ (extChartAt I_hs α).target) :
    chartPullbackZeroExtend (n := n) (M := M) α
        (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
          : C^∞⟮I_hs, M; ℝ⟯) x * u x) y =
      chartPushed (n := n) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M) α u y := by
  classical
  rw [chartSmoothExt_local_apply_of_mem_target (n := n) (M := M) α _ hy]
  unfold chartPushed
  rfl

omit [IsManifold (𝓡∂ n) ∞ M] [T2Space M] [SigmaCompactSpace M] in
private lemma chartSmoothExt_local_eq_zero_off_image_tsupport
    (α : M) {f : M → ℝ}
    (_hf_supp : tsupport f ⊆ (chartAt (EuclideanHalfSpace n) α).source)
    {y : EuclideanSpace ℝ (Fin n)}
    (hy_off : y ∉ (extChartAt I_hs α) '' (tsupport f)) :
    chartPullbackZeroExtend (n := n) (M := M) α f y = 0 := by
  classical
  by_cases hy_target : y ∈ (extChartAt I_hs α).target
  · rw [chartSmoothExt_local_apply_of_mem_target (n := n) (M := M) α f hy_target]
    by_contra hne
    apply hy_off
    have hsymm_in_supp : (extChartAt I_hs α).symm y ∈ tsupport f :=
      subset_tsupport _ (Function.mem_support.mpr hne)
    have hy_eq : (extChartAt I_hs α) ((extChartAt I_hs α).symm y) = y :=
      (extChartAt I_hs α).right_inv hy_target
    refine ⟨(extChartAt I_hs α).symm y, hsymm_in_supp, hy_eq⟩
  · exact chartSmoothExt_local_apply_of_notMem_target (n := n) (M := M) α f hy_target

private def chartSmoothExtInteriorSupport_local
    (α : M) (f : M → ℝ) : Prop :=
  (extChartAt I_hs α) '' (tsupport f) ⊆
    DifferentialGeometry.Analysis.Sobolev.Euclidean.openHalfSpace (d := n)

omit [IsManifold (𝓡∂ n) ∞ M] [T2Space M] [SigmaCompactSpace M] in
private lemma chartSmoothExtInteriorSupport_image_subset_interior_local
    {β : M} {f : M → ℝ}
    (hf_supp : tsupport f ⊆ (chartAt (EuclideanHalfSpace n) β).source)
    (h_int : chartSmoothExtInteriorSupport_local (n := n) (M := M) β f) :
    (extChartAt I_hs β) '' (tsupport f) ⊆
      DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
        (chartTargetEuclid (n := n) (M := M) β) := by
  rintro y ⟨x, hx, rfl⟩
  refine ⟨?_, h_int ⟨x, hx, rfl⟩⟩
  have h_src : x ∈ (extChartAt I_hs β).source := by
    rw [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
      (I := I_hs) (M := M)]
    exact hf_supp hx
  exact (extChartAt I_hs β).map_source h_src

private lemma pou_mul_subset_chart_source_local
    (β : M) (u : M → ℝ) :
    tsupport (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M β
        : C^∞⟮I_hs, M; ℝ⟯) x * u x) ⊆
      (chartAt (EuclideanHalfSpace n) β).source := by
  have h1 : tsupport (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M β
        : C^∞⟮I_hs, M; ℝ⟯) x * u x) ⊆
      tsupport ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M β
        : C^∞⟮I_hs, M; ℝ⟯) : M → ℝ) := by
    have h_eq : (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M β
        : C^∞⟮I_hs, M; ℝ⟯) x * u x) =
        (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M β
          : C^∞⟮I_hs, M; ℝ⟯) x • u x) := by funext x; rfl
    rw [h_eq]
    exact tsupport_smul_subset_left
      (f := fun x : M => ((DifferentialGeometry.Integral.Measure.chartAtlasPOU
        I_hs M β : C^∞⟮I_hs, M; ℝ⟯) : M → ℝ) x) (g := u)
  exact h1.trans (DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I_hs M β)

omit [T2Space M] [SigmaCompactSpace M] in
private lemma contDiffOn_chartSmoothExt_local_formula
    (α : M) {f : M → ℝ} (hf : ContMDiff I_hs 𝓘(ℝ, ℝ) ∞ f) :
    ContDiffOn ℝ ∞
        (fun y : EuclideanSpace ℝ (Fin n) => f ((extChartAt I_hs α).symm y))
        (extChartAt I_hs α).target := by
  classical
  exact DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE_contDiffOn
    (I := I_hs) α hf

omit [T2Space M] [SigmaCompactSpace M] in
private lemma contDiffAt_chartSmoothExt_local_of_mem_interior_target
    (α : M) {f : M → ℝ} (hf : ContMDiff I_hs 𝓘(ℝ, ℝ) ∞ f)
    {y : EuclideanSpace ℝ (Fin n)}
    (hy : y ∈ DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
        (chartTargetEuclid (n := n) (M := M) α)) :
    ContDiffAt ℝ ∞ (chartPullbackZeroExtend (n := n) (M := M) α f) y := by
  classical
  have hOpen : IsOpen (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
      (d := n) (chartTargetEuclid (n := n) (M := M) α)) := by
    apply DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace_isOpen
    exact chartTargetEuclid_isHalfSpaceRelOpen (n := n) (M := M) α
  have hy_target : y ∈ (extChartAt I_hs α).target := hy.1
  have hContDiffOn := contDiffOn_chartSmoothExt_local_formula (n := n) (M := M) α hf
  have h_within : ContDiffWithinAt ℝ ∞
      (fun y : EuclideanSpace ℝ (Fin n) => f ((extChartAt I_hs α).symm y))
      (extChartAt I_hs α).target y := hContDiffOn y hy_target
  have hInt_sub : DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
      (d := n) (chartTargetEuclid (n := n) (M := M) α) ⊆ (extChartAt I_hs α).target := by
    intro z hz
    exact hz.1
  have h_within_int : ContDiffWithinAt ℝ ∞
      (fun y : EuclideanSpace ℝ (Fin n) => f ((extChartAt I_hs α).symm y))
      (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
        (chartTargetEuclid (n := n) (M := M) α)) y :=
    h_within.mono hInt_sub
  have h_contDiffAt : ContDiffAt ℝ ∞
      (fun y : EuclideanSpace ℝ (Fin n) => f ((extChartAt I_hs α).symm y)) y :=
    h_within_int.contDiffAt (hOpen.mem_nhds hy)
  apply h_contDiffAt.congr_of_eventuallyEq
  filter_upwards [hOpen.mem_nhds hy] with z hz
  rw [chartSmoothExt_local_apply_of_mem_target (n := n) (M := M) α f hz.1]

omit [IsManifold (𝓡∂ n) ∞ M] [T2Space M] [SigmaCompactSpace M] in
private lemma contDiffAt_chartSmoothExt_local_of_notMem_image_tsupport
    (α : M) {f : M → ℝ}
    (hf_supp : tsupport f ⊆ (chartAt (EuclideanHalfSpace n) α).source)
    (hf_compact : IsCompact (tsupport f)) {y : EuclideanSpace ℝ (Fin n)}
    (hy_off : y ∉ (extChartAt I_hs α) '' (tsupport f)) :
    ContDiffAt ℝ ∞ (chartPullbackZeroExtend (n := n) (M := M) α f) y := by
  classical
  set K : Set (EuclideanSpace ℝ (Fin n)) := (extChartAt I_hs α) '' (tsupport f)
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
  apply ContDiffAt.congr_of_eventuallyEq (f := fun _ : EuclideanSpace ℝ (Fin n) => (0 : ℝ))
    contDiffAt_const
  filter_upwards [hK_compl_open.mem_nhds hy_compl] with z hz
  exact chartSmoothExt_local_eq_zero_off_image_tsupport
    (n := n) (M := M) α (f := f) hf_supp hz

variable [CompactSpace M]

omit [T2Space M] [SigmaCompactSpace M] in
private lemma contDiff_chartSmoothExt_local
    (α : M) {f : M → ℝ} (hf : ContMDiff I_hs 𝓘(ℝ, ℝ) ∞ f)
    (hf_supp : tsupport f ⊆ (chartAt (EuclideanHalfSpace n) α).source)
    (h_int : chartSmoothExtInteriorSupport_local (n := n) (M := M) α f) :
    ContDiff ℝ ∞ (chartPullbackZeroExtend (n := n) (M := M) α f) := by
  classical
  rw [contDiff_iff_contDiffAt]
  intro y
  set K : Set (EuclideanSpace ℝ (Fin n)) := (extChartAt I_hs α) '' (tsupport f)
  by_cases hyK : y ∈ K
  · have hy_int : y ∈
        DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
          (chartTargetEuclid (n := n) (M := M) α) :=
      chartSmoothExtInteriorSupport_image_subset_interior_local
        (n := n) (M := M) hf_supp h_int hyK
    exact contDiffAt_chartSmoothExt_local_of_mem_interior_target
      (n := n) (M := M) α hf hy_int
  · have hf_compact : IsCompact (tsupport f) := (isClosed_tsupport _).isCompact
    exact contDiffAt_chartSmoothExt_local_of_notMem_image_tsupport
      (n := n) (M := M) α hf_supp hf_compact hyK

omit [IsManifold (𝓡∂ n) ∞ M] [T2Space M] [SigmaCompactSpace M] in
private lemma image_extChartAt_tsupport_compact_local
    {f : M → ℝ} {α : M}
    (hf_supp : tsupport f ⊆ (chartAt (EuclideanHalfSpace n) α).source) :
    IsCompact ((extChartAt I_hs α) '' (tsupport f)) := by
  have h_supp_compact : IsCompact (tsupport f) := (isClosed_tsupport _).isCompact
  have h_supp_ext_src : tsupport f ⊆ (extChartAt I_hs α).source := by
    intro x hx
    rw [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
      (I := I_hs) (M := M)]
    exact hf_supp hx
  have h_cont : ContinuousOn (extChartAt I_hs α) (tsupport f) :=
    (continuousOn_extChartAt α).mono h_supp_ext_src
  exact h_supp_compact.image_of_continuousOn h_cont

omit [IsManifold (𝓡∂ n) ∞ M] [T2Space M] [SigmaCompactSpace M] in
private lemma hasCompactSupport_chartSmoothExt_local
    (α : M) {f : M → ℝ}
    (hf_supp : tsupport f ⊆ (chartAt (EuclideanHalfSpace n) α).source) :
    HasCompactSupport (chartPullbackZeroExtend (n := n) (M := M) α f) := by
  classical
  set K : Set (EuclideanSpace ℝ (Fin n)) := (extChartAt I_hs α) '' (tsupport f)
  have hK_compact : IsCompact K :=
    image_extChartAt_tsupport_compact_local (n := n) (M := M) (f := f) (α := α) hf_supp
  apply HasCompactSupport.of_support_subset_isCompact hK_compact
  intro y hy_supp
  by_contra hyK
  apply hy_supp
  exact chartSmoothExt_local_eq_zero_off_image_tsupport
    (n := n) (M := M) α (f := f) hf_supp hyK

omit [IsManifold (𝓡∂ n) ∞ M] [T2Space M] [SigmaCompactSpace M] in
private lemma tsupport_chartSmoothExt_local
    (α : M) {f : M → ℝ}
    (hf_supp : tsupport f ⊆ (chartAt (EuclideanHalfSpace n) α).source) :
    tsupport (chartPullbackZeroExtend (n := n) (M := M) α f) ⊆
      (extChartAt I_hs α) '' (tsupport f) := by
  classical
  set K : Set (EuclideanSpace ℝ (Fin n)) := (extChartAt I_hs α) '' (tsupport f)
  have hK_compact : IsCompact K :=
    image_extChartAt_tsupport_compact_local (n := n) (M := M) (f := f) (α := α) hf_supp
  have hK_closed : IsClosed K := hK_compact.isClosed
  have h_supp_sub : Function.support (chartPullbackZeroExtend (n := n) (M := M) α f) ⊆ K := by
    intro y hy
    by_contra hyK
    apply hy
    exact chartSmoothExt_local_eq_zero_off_image_tsupport
      (n := n) (M := M) α (f := f) hf_supp hyK
  rw [tsupport]
  exact hK_closed.closure_subset_iff.mpr h_supp_sub

omit [CompactSpace M] in

private lemma chartSmoothExt_ae_eq_chartPushed_interior_local
    (α : M) (u : M → ℝ) :
    chartPullbackZeroExtend (n := n) (M := M) α
        (fun x : M => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
          : C^∞⟮I_hs, M; ℝ⟯) x * u x) =ᵐ[volume.restrict
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
          (chartTargetEuclid (n := n) (M := M) α))]
      chartPushed (n := n) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M) α u := by
  have hOpen : IsOpen (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
      (chartTargetEuclid (n := n) (M := M) α)) := by
    apply DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace_isOpen
    exact chartTargetEuclid_isHalfSpaceRelOpen (n := n) (M := M) α
  refine (MeasureTheory.ae_restrict_iff' hOpen.measurableSet).mpr ?_
  refine Filter.Eventually.of_forall ?_
  intro y hy
  exact chartSmoothExt_local_eq_chartPushed_on_target α u hy.1

omit [CompactSpace M] in
theorem wkpNormChart_eq_finset_sum_withBoundary
    [CompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I_hs M)
    (k : ℕ) {p : ℝ≥0∞} (hp : 1 ≤ p) (u : M → ℝ) :
    wkpNormChart (n := n) (M := M) g k p u =
      ∑ α ∈ DifferentialGeometry.Integral.Measure.chartAtlasPOU_finset
              (I := I_hs) (M := M),
        DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace
          (d := n) k p
          (chartPushed (n := n) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M) α u)
          (chartTargetEuclid (n := n) (M := M) α) := by
  classical
  unfold wkpNormChart
  set f : M → ℝ≥0∞ := fun α =>
    DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace
      (d := n) k p
      (chartPushed (n := n) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M) α u)
      (chartTargetEuclid (n := n) (M := M) α) with hf_def
  have hf_zero_off : ∀ α : M, α ∉
      DifferentialGeometry.Integral.Measure.chartAtlasPOU_finset
        (I := I_hs) (M := M) → f α = 0 := by
    intro α hα
    have hρ_zero : ∀ x : M, (DifferentialGeometry.Integral.Measure.chartAtlasPOU
        I_hs M α : M → ℝ) x = 0 := by
      intro x
      exact DifferentialGeometry.Integral.Measure.chartAtlasPOU_weight_zero_of_notMem
        (I := I_hs) (M := M) hα x
    have hChartPushed_zero : chartPushed (n := n) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M) α u =
        (fun _ => (0 : ℝ)) := by
      funext y
      unfold chartPushed
      rw [hρ_zero]
      ring
    change DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace
      (d := n) k p
      (chartPushed (n := n) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M) α u)
      (chartTargetEuclid (n := n) (M := M) α) = 0
    rw [hChartPushed_zero]
    exact DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace_zero_fun_zero
      (d := n) hp
      (chartTargetEuclid_isHalfSpaceRelOpen (n := n) (M := M) α)
  rw [tsum_eq_sum hf_zero_off]

omit [CompactSpace M] in
theorem mul_smooth_chart_bound_explicit_form_withBoundary_of_per_chart
    [CompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I_hs M)
    {p : ℝ} (hp : (n : ℝ) < p)
    (Bα : M → ℝ)
    (hBα_nn : ∀ α ∈ DifferentialGeometry.Integral.Measure.chartAtlasPOU_finset
              (I := I_hs) (M := M), 0 ≤ Bα α)
    (hBα_per_chart : ∀ α ∈ DifferentialGeometry.Integral.Measure.chartAtlasPOU_finset
                (I := I_hs) (M := M),
        ∀ {u v : M → ℝ}, ContMDiff I_hs 𝓘(ℝ, ℝ) ∞ u → ContMDiff I_hs 𝓘(ℝ, ℝ) ∞ v →
          AllChartsInteriorSupport (n := n) (M := M) u →
          AllChartsInteriorSupport (n := n) (M := M) v →
          ∀ {uMax vMax : ℝ}, 0 ≤ uMax → 0 ≤ vMax →
            (∀ x : M, ‖u x‖ ≤ uMax) → (∀ x : M, ‖v x‖ ≤ vMax) →
            DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace
                (d := n) 1 (ENNReal.ofReal p)
                (chartPushed (n := n) (M := M)
                  (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M) α
                  (fun x => u x * v x))
                (chartTargetEuclid (n := n) (M := M) α) ≤
              ENNReal.ofReal vMax *
                DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace
                  (d := n) 1 (ENNReal.ofReal p)
                  (chartPushed (n := n) (M := M)
                    (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M) α u)
                  (chartTargetEuclid (n := n) (M := M) α) +
              ENNReal.ofReal uMax *
                DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace
                  (d := n) 1 (ENNReal.ofReal p)
                  (chartPushed (n := n) (M := M)
                    (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M) α v)
                  (chartTargetEuclid (n := n) (M := M) α) +
              ENNReal.ofReal (Bα α * uMax * vMax)) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ {u v : M → ℝ}, ContMDiff I_hs 𝓘(ℝ, ℝ) ∞ u → ContMDiff I_hs 𝓘(ℝ, ℝ) ∞ v →
        AllChartsInteriorSupport (n := n) (M := M) u →
        AllChartsInteriorSupport (n := n) (M := M) v →
        ∀ {uMax vMax : ℝ}, 0 ≤ uMax → 0 ≤ vMax →
          (∀ x : M, ‖u x‖ ≤ uMax) → (∀ x : M, ‖v x‖ ≤ vMax) →
          wkpNormChart (n := n) (M := M) g 1 (ENNReal.ofReal p)
              (fun x => u x * v x) ≤
            ENNReal.ofReal vMax *
              wkpNormChart (n := n) (M := M) g 1 (ENNReal.ofReal p) u +
            ENNReal.ofReal uMax *
              wkpNormChart (n := n) (M := M) g 1 (ENNReal.ofReal p) v +
            ENNReal.ofReal (B * uMax * vMax) := by
  classical
  have hd_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast NeZero.pos n
  have hd_one_le : (1 : ℝ) ≤ (n : ℝ) := by
    have : 1 ≤ n := NeZero.one_le
    exact_mod_cast this
  have hp_pos : 0 < p := lt_of_le_of_lt hd_pos.le hp
  have hp_one : (1 : ℝ) ≤ p := by linarith
  have hp_enn_one : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from by simp]
    exact ENNReal.ofReal_le_ofReal hp_one
  set S : Finset M :=
    DifferentialGeometry.Integral.Measure.chartAtlasPOU_finset (I := I_hs) (M := M)
    with hS_def
  refine ⟨∑ α ∈ S, Bα α, ?_, ?_⟩
  · exact Finset.sum_nonneg (fun α hα => hBα_nn α hα)
  intro u v hu hv h_int_u h_int_v uMax vMax huMax_nn hvMax_nn hu_bound hv_bound
  rw [wkpNormChart_eq_finset_sum_withBoundary (n := n) (M := M) g 1 hp_enn_one
      (fun x => u x * v x),
    wkpNormChart_eq_finset_sum_withBoundary (n := n) (M := M) g 1 hp_enn_one u,
    wkpNormChart_eq_finset_sum_withBoundary (n := n) (M := M) g 1 hp_enn_one v]
  have hBα_bound : ∀ α ∈ S,
      DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace
          (d := n) 1 (ENNReal.ofReal p)
          (chartPushed (n := n) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M) α
            (fun x => u x * v x))
          (chartTargetEuclid (n := n) (M := M) α) ≤
        ENNReal.ofReal vMax *
          DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace
            (d := n) 1 (ENNReal.ofReal p)
            (chartPushed (n := n) (M := M)
              (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M) α u)
            (chartTargetEuclid (n := n) (M := M) α) +
        ENNReal.ofReal uMax *
          DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace
            (d := n) 1 (ENNReal.ofReal p)
            (chartPushed (n := n) (M := M)
              (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M) α v)
            (chartTargetEuclid (n := n) (M := M) α) +
        ENNReal.ofReal (Bα α * uMax * vMax) := by
    intro α hα
    exact hBα_per_chart α hα hu hv h_int_u h_int_v huMax_nn hvMax_nn hu_bound hv_bound
  refine (Finset.sum_le_sum (fun α hα => hBα_bound α hα)).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  set X : M → ℝ≥0∞ := fun α =>
    DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace
      (d := n) 1 (ENNReal.ofReal p)
      (chartPushed (n := n) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M) α u)
      (chartTargetEuclid (n := n) (M := M) α) with hX_def
  set Y : M → ℝ≥0∞ := fun α =>
    DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace
      (d := n) 1 (ENNReal.ofReal p)
      (chartPushed (n := n) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M) α v)
      (chartTargetEuclid (n := n) (M := M) α) with hY_def
  rw [show (∑ α ∈ S, ENNReal.ofReal vMax * X α) =
        ENNReal.ofReal vMax * ∑ α ∈ S, X α from
        (Finset.mul_sum _ _ _).symm,
      show (∑ α ∈ S, ENNReal.ofReal uMax * Y α) =
        ENNReal.ofReal uMax * ∑ α ∈ S, Y α from
        (Finset.mul_sum _ _ _).symm]
  refine add_le_add (le_refl _) ?_
  have h_sum_ofReal : ∑ α ∈ S, ENNReal.ofReal (Bα α * uMax * vMax) =
      ENNReal.ofReal (∑ α ∈ S, Bα α * uMax * vMax) := by
    refine (ENNReal.ofReal_sum_of_nonneg ?_).symm
    intro α hα
    exact mul_nonneg (mul_nonneg (hBα_nn α hα) huMax_nn) hvMax_nn
  rw [h_sum_ofReal]
  have h_factor : ∑ α ∈ S, Bα α * uMax * vMax = (∑ α ∈ S, Bα α) * uMax * vMax := by
    rw [show (∑ α ∈ S, Bα α * uMax * vMax) = ∑ α ∈ S, Bα α * (uMax * vMax) from
      Finset.sum_congr rfl (fun α _ => by ring),
      ← Finset.sum_mul]
    ring
  rw [h_factor]

omit [CompactSpace M] in
theorem mul_smooth_chart_bound_withBoundary_interior_of_per_chart
    [CompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I_hs M)
    {p : ℝ} (hp : (n : ℝ) < p)
    (Bα : M → ℝ)
    (hBα_nn : ∀ α ∈ DifferentialGeometry.Integral.Measure.chartAtlasPOU_finset
              (I := I_hs) (M := M), 0 ≤ Bα α)
    (hBα_per_chart : ∀ α ∈ DifferentialGeometry.Integral.Measure.chartAtlasPOU_finset
                (I := I_hs) (M := M),
        ∀ {u v : M → ℝ}, ContMDiff I_hs 𝓘(ℝ, ℝ) ∞ u → ContMDiff I_hs 𝓘(ℝ, ℝ) ∞ v →
          AllChartsInteriorSupport (n := n) (M := M) u →
          AllChartsInteriorSupport (n := n) (M := M) v →
          ∀ {uMax vMax : ℝ}, 0 ≤ uMax → 0 ≤ vMax →
            (∀ x : M, ‖u x‖ ≤ uMax) → (∀ x : M, ‖v x‖ ≤ vMax) →
            DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace
                (d := n) 1 (ENNReal.ofReal p)
                (chartPushed (n := n) (M := M)
                  (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M) α
                  (fun x => u x * v x))
                (chartTargetEuclid (n := n) (M := M) α) ≤
              ENNReal.ofReal vMax *
                DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace
                  (d := n) 1 (ENNReal.ofReal p)
                  (chartPushed (n := n) (M := M)
                    (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M) α u)
                  (chartTargetEuclid (n := n) (M := M) α) +
              ENNReal.ofReal uMax *
                DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace
                  (d := n) 1 (ENNReal.ofReal p)
                  (chartPushed (n := n) (M := M)
                    (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M) α v)
                  (chartTargetEuclid (n := n) (M := M) α) +
              ENNReal.ofReal (Bα α * uMax * vMax))
    (hMembership : ∀ {u : M → ℝ}, ContMDiff I_hs 𝓘(ℝ, ℝ) ∞ u →
        AllChartsInteriorSupport (n := n) (M := M) u →
        MemWkpChart (n := n) (M := M) g 1 (ENNReal.ofReal p) u) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {u v : M → ℝ},
        ContMDiff I_hs 𝓘(ℝ, ℝ) ∞ u → ContMDiff I_hs 𝓘(ℝ, ℝ) ∞ v →
        AllChartsInteriorSupport (n := n) (M := M) u →
        AllChartsInteriorSupport (n := n) (M := M) v →
        wkpNormChart (n := n) (M := M) g 1 (ENNReal.ofReal p) (fun x => u x * v x) ≤
          ENNReal.ofReal C *
            wkpNormChart (n := n) (M := M) g 1 (ENNReal.ofReal p) u *
            wkpNormChart (n := n) (M := M) g 1 (ENNReal.ofReal p) v := by
  classical
  obtain ⟨B, hB_nn, hB_bound⟩ :=
    mul_smooth_chart_bound_explicit_form_withBoundary_of_per_chart
      (n := n) (M := M) g hp Bα hBα_nn hBα_per_chart
  obtain ⟨M_M, hM_M_nn, hM_M_bound⟩ :=
    smooth_manifold_morrey_sup_bound_uniform_withBoundary
      (n := n) (M := M) g hp
  set C : ℝ := 2 * M_M + B * M_M ^ 2 with hC_def
  have hC_nn : 0 ≤ C := by
    have h1 : 0 ≤ 2 * M_M := mul_nonneg (by norm_num) hM_M_nn
    have h2 : 0 ≤ B * M_M ^ 2 := mul_nonneg hB_nn (sq_nonneg _)
    linarith
  refine ⟨C, hC_nn, ?_⟩
  intro u v hu hv h_int_u h_int_v
  have hd_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast NeZero.pos n
  have hd_one_le : (1 : ℝ) ≤ (n : ℝ) := by
    have : 1 ≤ n := NeZero.one_le
    exact_mod_cast this
  have hp_pos : 0 < p := lt_of_le_of_lt hd_pos.le hp
  have hp_one : (1 : ℝ) ≤ p := by linarith
  have hp_enn_one : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from by simp]
    exact ENNReal.ofReal_le_ofReal hp_one
  set NU : ℝ≥0∞ := wkpNormChart (n := n) (M := M) g 1 (ENNReal.ofReal p) u with hNU_def
  set NV : ℝ≥0∞ := wkpNormChart (n := n) (M := M) g 1 (ENNReal.ofReal p) v with hNV_def
  have hNU_lt : NU < ⊤ :=
    wkpNormChart_lt_top_of_memWkpChart (n := n) (M := M) g hp_enn_one (hMembership hu h_int_u)
  have hNV_lt : NV < ⊤ :=
    wkpNormChart_lt_top_of_memWkpChart (n := n) (M := M) g hp_enn_one (hMembership hv h_int_v)
  have hNU_ne_top : NU ≠ ⊤ := hNU_lt.ne
  have hNV_ne_top : NV ≠ ⊤ := hNV_lt.ne
  set uMax : ℝ := M_M * NU.toReal with huMax_def
  set vMax : ℝ := M_M * NV.toReal with hvMax_def
  have huMax_nn : 0 ≤ uMax := mul_nonneg hM_M_nn ENNReal.toReal_nonneg
  have hvMax_nn : 0 ≤ vMax := mul_nonneg hM_M_nn ENNReal.toReal_nonneg
  have hu_bound : ∀ x : M, ‖u x‖ ≤ uMax := fun x => hM_M_bound hu h_int_u x
  have hv_bound : ∀ x : M, ‖v x‖ ≤ vMax := fun x => hM_M_bound hv h_int_v x
  have h_explicit := hB_bound hu hv h_int_u h_int_v huMax_nn hvMax_nn hu_bound hv_bound
  refine h_explicit.trans ?_
  have h_ofReal_vMax : ENNReal.ofReal vMax = ENNReal.ofReal M_M * NV := by
    rw [hvMax_def]
    rw [ENNReal.ofReal_mul hM_M_nn, ENNReal.ofReal_toReal hNV_ne_top]
  have h_ofReal_uMax : ENNReal.ofReal uMax = ENNReal.ofReal M_M * NU := by
    rw [huMax_def]
    rw [ENNReal.ofReal_mul hM_M_nn, ENNReal.ofReal_toReal hNU_ne_top]
  have h_ofReal_B_uMax_vMax : ENNReal.ofReal (B * uMax * vMax) =
      ENNReal.ofReal (B * M_M ^ 2) * NU * NV := by
    have h_eq : B * uMax * vMax = B * M_M ^ 2 * NU.toReal * NV.toReal := by
      rw [huMax_def, hvMax_def]
      ring
    rw [h_eq]
    have h_BM2_nn : 0 ≤ B * M_M ^ 2 := mul_nonneg hB_nn (sq_nonneg _)
    have h_BM2_NU_nn : 0 ≤ B * M_M ^ 2 * NU.toReal :=
      mul_nonneg h_BM2_nn ENNReal.toReal_nonneg
    rw [ENNReal.ofReal_mul h_BM2_NU_nn, ENNReal.ofReal_mul h_BM2_nn,
      ENNReal.ofReal_toReal hNU_ne_top, ENNReal.ofReal_toReal hNV_ne_top]
  rw [h_ofReal_vMax, h_ofReal_uMax, h_ofReal_B_uMax_vMax]
  have h_sum_le : ENNReal.ofReal M_M + ENNReal.ofReal M_M + ENNReal.ofReal (B * M_M ^ 2) ≤
      ENNReal.ofReal C := by
    rw [show (ENNReal.ofReal M_M + ENNReal.ofReal M_M : ℝ≥0∞) =
      ENNReal.ofReal (M_M + M_M) from
      (ENNReal.ofReal_add hM_M_nn hM_M_nn).symm,
      show (ENNReal.ofReal (M_M + M_M) + ENNReal.ofReal (B * M_M ^ 2) : ℝ≥0∞) =
        ENNReal.ofReal ((M_M + M_M) + (B * M_M ^ 2)) from
      (ENNReal.ofReal_add (by linarith) (mul_nonneg hB_nn (sq_nonneg _))).symm]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hC_def]
    linarith
  have h_LHS_eq : ENNReal.ofReal M_M * NV * NU + ENNReal.ofReal M_M * NU * NV +
      ENNReal.ofReal (B * M_M ^ 2) * NU * NV =
    (ENNReal.ofReal M_M + ENNReal.ofReal M_M + ENNReal.ofReal (B * M_M ^ 2)) * NU * NV := by
    ring
  rw [h_LHS_eq]
  exact mul_le_mul' (mul_le_mul' h_sum_le (le_refl _)) (le_refl _)

omit [CompactSpace M] in
theorem MemWkpChart_of_contMDiff_AllChartsInteriorSupport
    [CompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I_hs M)
    {p : ℝ≥0∞} (hp : 1 ≤ p)
    {u : M → ℝ} (hu : ContMDiff I_hs 𝓘(ℝ, ℝ) ∞ u)
    (h_int : AllChartsInteriorSupport (n := n) (M := M) u) :
    MemWkpChart (n := n) (M := M) g 1 p u := by
  classical
  intro β
  set fβ : M → ℝ := fun x : M =>
    (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M β
      : C^∞⟮I_hs, M; ℝ⟯) x * u x
  have hfβ_smooth : ContMDiff I_hs 𝓘(ℝ, ℝ) ∞ fβ :=
    ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M β
        : C^∞⟮I_hs, M; ℝ⟯).contMDiff).mul hu
  have hΩ_open : IsOpen
      (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
        (chartTargetEuclid (n := n) (M := M) β)) := by
    apply DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace_isOpen
    exact chartTargetEuclid_isHalfSpaceRelOpen (n := n) (M := M) β
  change DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
    (d := n) 1 p
    (chartPushed (n := n) (M := M)
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M) β u)
    (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
      (chartTargetEuclid (n := n) (M := M) β))
  have h_pou_supp_chart_src : tsupport fβ ⊆ (chartAt (EuclideanHalfSpace n) β).source :=
    pou_mul_subset_chart_source_local β u
  have h_int_image : (extChartAt I_hs β) '' (tsupport fβ) ⊆
      DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
        (chartTargetEuclid (n := n) (M := M) β) :=
    chartSmoothExtInteriorSupport_image_subset_interior_local
      (β := β) h_pou_supp_chart_src (h_int β)
  set ext_β : EuclideanSpace ℝ (Fin n) → ℝ := chartPullbackZeroExtend β fβ with hext_β_def
  have hext_β_smooth : ContDiff ℝ ∞ ext_β :=
    contDiff_chartSmoothExt_local β hfβ_smooth h_pou_supp_chart_src (h_int β)
  have hext_β_compact : HasCompactSupport ext_β :=
    hasCompactSupport_chartSmoothExt_local β h_pou_supp_chart_src
  have hext_β_supp : tsupport ext_β ⊆
      DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
        (chartTargetEuclid (n := n) (M := M) β) :=
    (tsupport_chartSmoothExt_local β h_pou_supp_chart_src).trans h_int_image
  have hext_β_W1p : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := n) 1 p ext_β
      (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
        (chartTargetEuclid (n := n) (M := M) β)) :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_of_smooth_compactSupport_pub
      (d := n) hΩ_open hext_β_smooth hext_β_compact hext_β_supp hp 1
  have h_ae : ext_β =ᵐ[volume.restrict
      (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
        (chartTargetEuclid (n := n) (M := M) β))]
      chartPushed (n := n) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M) β u :=
    chartSmoothExt_ae_eq_chartPushed_interior_local β u
  exact (DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_congr_ae
    (d := n) hp hΩ_open h_ae).mp hext_β_W1p

omit [CompactSpace M] in
theorem mul_smooth_chart_bound_withBoundary_interior
    [CompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I_hs M)
    {p : ℝ} (hp : (n : ℝ) < p)
    (Bα : M → ℝ)
    (hBα_nn : ∀ α ∈ DifferentialGeometry.Integral.Measure.chartAtlasPOU_finset
              (I := I_hs) (M := M), 0 ≤ Bα α)
    (hBα_per_chart : ∀ α ∈ DifferentialGeometry.Integral.Measure.chartAtlasPOU_finset
                (I := I_hs) (M := M),
        ∀ {u v : M → ℝ}, ContMDiff I_hs 𝓘(ℝ, ℝ) ∞ u → ContMDiff I_hs 𝓘(ℝ, ℝ) ∞ v →
          AllChartsInteriorSupport (n := n) (M := M) u →
          AllChartsInteriorSupport (n := n) (M := M) v →
          ∀ {uMax vMax : ℝ}, 0 ≤ uMax → 0 ≤ vMax →
            (∀ x : M, ‖u x‖ ≤ uMax) → (∀ x : M, ‖v x‖ ≤ vMax) →
            DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace
                (d := n) 1 (ENNReal.ofReal p)
                (chartPushed (n := n) (M := M)
                  (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M) α
                  (fun x => u x * v x))
                (chartTargetEuclid (n := n) (M := M) α) ≤
              ENNReal.ofReal vMax *
                DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace
                  (d := n) 1 (ENNReal.ofReal p)
                  (chartPushed (n := n) (M := M)
                    (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M) α u)
                  (chartTargetEuclid (n := n) (M := M) α) +
              ENNReal.ofReal uMax *
                DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace
                  (d := n) 1 (ENNReal.ofReal p)
                  (chartPushed (n := n) (M := M)
                    (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M) α v)
                  (chartTargetEuclid (n := n) (M := M) α) +
              ENNReal.ofReal (Bα α * uMax * vMax)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {u v : M → ℝ},
        ContMDiff I_hs 𝓘(ℝ, ℝ) ∞ u → ContMDiff I_hs 𝓘(ℝ, ℝ) ∞ v →
        AllChartsInteriorSupport (n := n) (M := M) u →
        AllChartsInteriorSupport (n := n) (M := M) v →
        wkpNormChart (n := n) (M := M) g 1 (ENNReal.ofReal p) (fun x => u x * v x) ≤
          ENNReal.ofReal C *
            wkpNormChart (n := n) (M := M) g 1 (ENNReal.ofReal p) u *
            wkpNormChart (n := n) (M := M) g 1 (ENNReal.ofReal p) v := by
  classical
  have hd_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast NeZero.pos n
  have hd_one_le : (1 : ℝ) ≤ (n : ℝ) := by
    have : 1 ≤ n := NeZero.one_le
    exact_mod_cast this
  have hp_pos : 0 < p := lt_of_le_of_lt hd_pos.le hp
  have hp_one : (1 : ℝ) ≤ p := by linarith
  have hp_enn_one : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from by simp]
    exact ENNReal.ofReal_le_ofReal hp_one
  exact mul_smooth_chart_bound_withBoundary_interior_of_per_chart
    (n := n) (M := M) g hp Bα hBα_nn hBα_per_chart
    (fun {u} hu h_int => MemWkpChart_of_contMDiff_AllChartsInteriorSupport
      (n := n) (M := M) g hp_enn_one hu h_int)

private noncomputable def chartLifted_local (α : M) (v : M → ℝ) :
    EuclideanSpace ℝ (Fin n) → ℝ := by
  classical
  exact fun y =>
    if y ∈ (extChartAt I_hs α).target then v ((extChartAt I_hs α).symm y) else 0

omit [IsManifold (𝓡∂ n) ∞ M] [T2Space M] [SigmaCompactSpace M] [CompactSpace M] in
private lemma chartLifted_local_apply_of_mem_target
    (α : M) (v : M → ℝ) {y : EuclideanSpace ℝ (Fin n)}
    (hy : y ∈ (extChartAt I_hs α).target) :
    chartLifted_local (n := n) (M := M) α v y = v ((extChartAt I_hs α).symm y) := by
  classical
  change (if y ∈ (extChartAt I_hs α).target then v ((extChartAt I_hs α).symm y)
    else 0) = v ((extChartAt I_hs α).symm y)
  rw [if_pos hy]

omit [IsManifold (𝓡∂ n) ∞ M] [T2Space M] [SigmaCompactSpace M] [CompactSpace M] in
private lemma chartLifted_local_apply_of_notMem_target
    (α : M) (v : M → ℝ) {y : EuclideanSpace ℝ (Fin n)}
    (hy : y ∉ (extChartAt I_hs α).target) :
    chartLifted_local (n := n) (M := M) α v y = 0 := by
  classical
  change (if y ∈ (extChartAt I_hs α).target then v ((extChartAt I_hs α).symm y)
    else 0) = 0
  rw [if_neg hy]

omit [CompactSpace M] in
private lemma chartPushed_eq_chartPushed_mul_chartLifted_local
    (α : M) (u v : M → ℝ) {y : EuclideanSpace ℝ (Fin n)}
    (hy : y ∈ (extChartAt I_hs α).target) :
    chartPushed (n := n) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M) α
        (fun x => u x * v x) y =
      chartPushed (n := n) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M) α u y *
        chartLifted_local (n := n) (M := M) α v y := by
  classical
  rw [chartLifted_local_apply_of_mem_target (n := n) (M := M) α v hy]
  unfold chartPushed
  ring

omit [IsManifold (𝓡∂ n) ∞ M] [T2Space M] [SigmaCompactSpace M] [CompactSpace M] in
private lemma chartLifted_local_apply_norm_le
    (α : M) (v : M → ℝ) {vMax : ℝ}
    (hv_bound : ∀ x : M, ‖v x‖ ≤ vMax) (hvMax_nn : 0 ≤ vMax)
    (y : EuclideanSpace ℝ (Fin n)) :
    ‖chartLifted_local (n := n) (M := M) α v y‖ ≤ vMax := by
  classical
  by_cases hy : y ∈ (extChartAt I_hs α).target
  · rw [chartLifted_local_apply_of_mem_target (n := n) (M := M) α v hy]
    exact hv_bound _
  · rw [chartLifted_local_apply_of_notMem_target (n := n) (M := M) α v hy, norm_zero]
    exact hvMax_nn

omit [IsManifold (𝓡∂ n) ∞ M] [T2Space M] [SigmaCompactSpace M] [CompactSpace M] in
private lemma chartLifted_local_eq_chartSmoothExt_local
    (α : M) (v : M → ℝ) :
    chartLifted_local (n := n) (M := M) α v =
      chartPullbackZeroExtend (n := n) (M := M) α v := by
  funext y; rfl

omit [CompactSpace M] in
private lemma chartPushed_mul_eq_chartPushed_mul_chartLifted_local_ae
    (α : M) (u v : M → ℝ) :
    (fun y : EuclideanSpace ℝ (Fin n) => chartPushed (n := n) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M) α
        (fun x => u x * v x) y) =ᵐ[volume.restrict
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
          (chartTargetEuclid (n := n) (M := M) α))]
      fun y : EuclideanSpace ℝ (Fin n) =>
        chartPushed (n := n) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M) α u y *
          chartLifted_local (n := n) (M := M) α v y := by
  classical
  have hΩ_open : IsOpen
      (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
        (chartTargetEuclid (n := n) (M := M) α)) := by
    apply DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace_isOpen
    exact chartTargetEuclid_isHalfSpaceRelOpen (n := n) (M := M) α
  refine (MeasureTheory.ae_restrict_iff' hΩ_open.measurableSet).mpr ?_
  refine Filter.Eventually.of_forall (fun y hy => ?_)
  exact chartPushed_eq_chartPushed_mul_chartLifted_local
    (n := n) (M := M) α u v hy.1

omit [CompactSpace M] in
private lemma eLpNorm_chartPushed_mul_le_vMax_eLpNorm_chartPushed_u
    (α : M) {u v : M → ℝ} {vMax : ℝ}
    (hv_bound : ∀ x : M, ‖v x‖ ≤ vMax) (_hvMax_nn : 0 ≤ vMax)
    (q : ℝ≥0∞) :
    eLpNorm (chartPushed (n := n) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M) α
        (fun x => u x * v x)) q
      (volume.restrict
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
          (chartTargetEuclid (n := n) (M := M) α))) ≤
      ENNReal.ofReal vMax *
        eLpNorm (chartPushed (n := n) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M) α u) q
        (volume.restrict
          (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
            (chartTargetEuclid (n := n) (M := M) α))) := by
  classical
  refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul (g := chartPushed (n := n) (M := M)
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M) α u)
    (c := vMax) ?_ q
  refine Filter.Eventually.of_forall (fun y => ?_)
  unfold chartPushed
  set ρy : ℝ := ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
    : C^∞⟮I_hs, M; ℝ⟯) : M → ℝ) ((extChartAt I_hs α).symm y) with hρy_def
  set xy : M := (extChartAt I_hs α).symm y with hxy_def
  have hρy_nn : 0 ≤ ρy := by
    rw [hρy_def]
    exact (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M).nonneg α xy
  have h_norm_uv : ‖ρy * (u xy * v xy)‖ = ρy * ‖u xy‖ * ‖v xy‖ := by
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hρy_nn,
      Real.norm_eq_abs, Real.norm_eq_abs, mul_assoc]
  have h_norm_v : ‖ρy * u xy‖ = ρy * ‖u xy‖ := by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hρy_nn, Real.norm_eq_abs]
  rw [h_norm_uv, h_norm_v]
  calc
    ρy * ‖u xy‖ * ‖v xy‖
        ≤ ρy * ‖u xy‖ * vMax := by
          gcongr
          exact hv_bound _
    _ = vMax * (ρy * ‖u xy‖) := by ring

end WithBoundary
end Sobolev
end Analysis
end DifferentialGeometry
