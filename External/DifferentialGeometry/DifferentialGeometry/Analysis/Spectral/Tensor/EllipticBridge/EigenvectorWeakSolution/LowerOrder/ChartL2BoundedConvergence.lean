import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.LowerOrder.ChartPouKernel


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold Set Filter MeasureTheory
open scoped Manifold Topology ContDiff BigOperators Matrix ENNReal NNReal
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open DifferentialGeometry.Analysis.Laplacian.MetricExtension hiding chartTargetEuclid

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

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma memLp_bdd_mul
    (α : M) {c : EuclN → ℝ} {C : ℝ} (hC : 0 ≤ C) (hc_bd : ∀ y, ‖c y‖ ≤ C)
    (hc_meas : AEStronglyMeasurable c (chartL2Measure (I := I) (M := M) α))
    {f : EuclN → ℝ}
    (hf : MemLp f 2 (chartL2Measure (I := I) (M := M) α)) :
    MemLp (fun y => c y * f y) 2 (chartL2Measure (I := I) (M := M) α) := by
  classical
  refine ⟨hc_meas.mul hf.1, ?_⟩
  have hpt : ∀ y : EuclN, ‖c y * f y‖ ≤ ‖(C : ℝ) • f y‖ := by
    intro y
    have h1 : ‖c y * f y‖ = ‖c y‖ * ‖f y‖ := norm_mul _ _
    have h2 : ‖(C : ℝ) • f y‖ = C * ‖f y‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hC]
    rw [h1, h2]
    exact mul_le_mul_of_nonneg_right (hc_bd y) (norm_nonneg _)
  have hmono := eLpNorm_mono (μ := chartL2Measure (I := I) (M := M) α)
    (p := 2) hpt
  calc eLpNorm (fun y => c y * f y) 2 (chartL2Measure (I := I) (M := M) α)
      ≤ eLpNorm ((C : ℝ) • f) 2 (chartL2Measure (I := I) (M := M) α) := hmono
    _ = ‖(C : ℝ)‖ₑ * eLpNorm f 2 (chartL2Measure (I := I) (M := M) α) :=
        eLpNorm_const_smul (C : ℝ) f 2 _
    _ < ⊤ := ENNReal.mul_lt_top (by simp) hf.2

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma eLpNorm_bdd_mul_le
    (α : M) {c : EuclN → ℝ} {C : ℝ} (hC : 0 ≤ C) (hc_bd : ∀ y, ‖c y‖ ≤ C)
    (f : EuclN → ℝ) :
    eLpNorm (fun y => c y * f y) 2 (chartL2Measure (I := I) (M := M) α) ≤
      ENNReal.ofReal C *
        eLpNorm f 2 (chartL2Measure (I := I) (M := M) α) := by
  classical
  have hpt : ∀ y : EuclN, ‖c y * f y‖ ≤ ‖(C : ℝ) • f y‖ := by
    intro y
    have h1 : ‖c y * f y‖ = ‖c y‖ * ‖f y‖ := norm_mul _ _
    have h2 : ‖(C : ℝ) • f y‖ = C * ‖f y‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hC]
    rw [h1, h2]
    exact mul_le_mul_of_nonneg_right (hc_bd y) (norm_nonneg _)
  calc eLpNorm (fun y => c y * f y) 2 (chartL2Measure (I := I) (M := M) α)
      ≤ eLpNorm ((C : ℝ) • f) 2 (chartL2Measure (I := I) (M := M) α) :=
        eLpNorm_mono hpt
    _ = ‖(C : ℝ)‖ₑ * eLpNorm f 2 (chartL2Measure (I := I) (M := M) α) :=
        eLpNorm_const_smul (C : ℝ) f 2 _
    _ = ENNReal.ofReal C *
          eLpNorm f 2 (chartL2Measure (I := I) (M := M) α) := by
        rw [Real.enorm_eq_ofReal hC]

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma tendsto_bdd_mul
    (α : M) {c : EuclN → ℝ} {C : ℝ} (hC : 0 ≤ C) (hc_bd : ∀ y, ‖c y‖ ≤ C)
    (hc_meas : AEStronglyMeasurable c (chartL2Measure (I := I) (M := M) α))
    {F : ℕ → Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)}
    {Flim : Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)}
    (hF : Filter.Tendsto F atTop (𝓝 Flim)) :
    Filter.Tendsto
      (fun n => (memLp_bdd_mul (I := I) (M := M) α hC hc_bd hc_meas
        (Lp.memLp (F n))).toLp (fun y => c y * (F n : EuclN → ℝ) y))
      atTop
      (𝓝 ((memLp_bdd_mul (I := I) (M := M) α hC hc_bd hc_meas
        (Lp.memLp Flim)).toLp (fun y => c y * (Flim : EuclN → ℝ) y))) := by
  classical
  refine Metric.tendsto_atTop.mpr (fun ε hε => ?_)
  have hCpos : (0 : ℝ) < C + 1 := by positivity
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hF (ε / (C + 1)) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have hdist_eq :
      dist
        ((memLp_bdd_mul (I := I) (M := M) α hC hc_bd hc_meas
          (Lp.memLp (F n))).toLp (fun y => c y * (F n : EuclN → ℝ) y))
        ((memLp_bdd_mul (I := I) (M := M) α hC hc_bd hc_meas
          (Lp.memLp Flim)).toLp (fun y => c y * (Flim : EuclN → ℝ) y)) =
      (eLpNorm
        (fun y => c y * (F n : EuclN → ℝ) y -
          c y * (Flim : EuclN → ℝ) y) 2
        (chartL2Measure (I := I) (M := M) α)).toReal := by
    rw [Lp.dist_def]
    refine congrArg ENNReal.toReal (eLpNorm_congr_ae ?_)
    filter_upwards [MemLp.coeFn_toLp (memLp_bdd_mul (I := I) (M := M) α hC
        hc_bd hc_meas (Lp.memLp (F n))),
      MemLp.coeFn_toLp (memLp_bdd_mul (I := I) (M := M) α hC hc_bd hc_meas
        (Lp.memLp Flim))] with y hy₁ hy₂
    rw [Pi.sub_apply, hy₁, hy₂]
  rw [hdist_eq]
  have hsub_eq :
      (fun y => c y * (F n : EuclN → ℝ) y - c y * (Flim : EuclN → ℝ) y) =
        (fun y => c y * ((F n : EuclN → ℝ) y - (Flim : EuclN → ℝ) y)) := by
    funext y; ring
  rw [hsub_eq]
  have hle := eLpNorm_bdd_mul_le (I := I) (M := M) α hC hc_bd
    (fun y => (F n : EuclN → ℝ) y - (Flim : EuclN → ℝ) y)
  have hsub_ae :
      (fun y => (F n : EuclN → ℝ) y - (Flim : EuclN → ℝ) y)
        =ᵐ[chartL2Measure (I := I) (M := M) α]
      (((F n) - Flim : Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
        EuclN → ℝ) :=
    (Lp.coeFn_sub (F n) Flim).symm
  have hdist_F :
      eLpNorm (fun y => (F n : EuclN → ℝ) y - (Flim : EuclN → ℝ) y) 2
          (chartL2Measure (I := I) (M := M) α) =
        ENNReal.ofReal (dist (F n) Flim) := by
    have hfin : eLpNorm
        (((F n) - Flim : Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
          EuclN → ℝ) 2 (chartL2Measure (I := I) (M := M) α) ≠ ⊤ :=
      (Lp.memLp ((F n) - Flim)).2.ne
    rw [eLpNorm_congr_ae hsub_ae, Lp.dist_def,
      ENNReal.ofReal_toReal ((eLpNorm_congr_ae hsub_ae) ▸ hfin)]
    exact (eLpNorm_congr_ae hsub_ae).symm
  rw [hdist_F] at hle
  have hfin : (ENNReal.ofReal C * ENNReal.ofReal (dist (F n) Flim)) ≠ ⊤ :=
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top).ne
  have hreal :
      (eLpNorm (fun y => c y *
          ((F n : EuclN → ℝ) y - (Flim : EuclN → ℝ) y)) 2
        (chartL2Measure (I := I) (M := M) α)).toReal ≤
        C * dist (F n) Flim := by
    refine (ENNReal.toReal_mono hfin hle).trans ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC,
      ENNReal.toReal_ofReal dist_nonneg]
  refine lt_of_le_of_lt hreal ?_
  have hd : dist (F n) Flim < ε / (C + 1) := hN n hn
  calc C * dist (F n) Flim
      ≤ (C + 1) * dist (F n) Flim :=
        mul_le_mul_of_nonneg_right (by linarith) dist_nonneg
    _ < (C + 1) * (ε / (C + 1)) :=
        mul_lt_mul_of_pos_left hd hCpos
    _ = ε := by field_simp

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
lemma tensorChartComponent_contDiff'
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ContDiff ℝ (⊤ : ℕ∞)
      (tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx) :=
  (contMDiff_iff_contDiff (n := (⊤ : ℕ∞))).mp
    (tensorChartComponent_contMDiff (I := I) (M := M) g r s S α Idx Jdx)

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma tensorChartComponent_tsupport_subset_chartPouKernel
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tsupport (tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx) ⊆
      chartPouKernel (I := I) (M := M) α := by
  classical
  have hsupp : Function.support
      (tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx) ⊆
      chartPouKernel (I := I) (M := M) α := by
    intro z hz
    by_contra hzk
    exact hz (tensorChartComponent_eq_zero_off_chartPouKernel
      (I := I) (M := M) g r s S α Idx Jdx hzk)
  exact closure_minimal hsupp
    (chartPouKernel_isCompact (I := I) (M := M) α).isClosed

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
lemma chosenWeakPartial'_tensorChartComponent_ae_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (k : Fin (Module.finrank ℝ E)) :
    chosenWeakPartial' (d := Module.finrank ℝ E) 2 k
        (tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx)
        (chartTargetEuclid (I := I) (M := M) α)
      =ᵐ[chartL2Measure (I := I) (M := M) α]
      euclidPartial (E := E) k
        (tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx) := by
  classical
  set u : EuclN → ℝ :=
    tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx with hu_def
  have hu_smooth : ContDiff ℝ (⊤ : ℕ∞) u :=
    tensorChartComponent_contDiff' (I := I) (M := M) g r s S α Idx Jdx
  have hu_cpt : HasCompactSupport u :=
    tensorChartComponent_hasCompactSupport (I := I) (M := M) g r s S α Idx Jdx
  have hu_tsupp : tsupport u ⊆ chartTargetEuclid (I := I) (M := M) α :=
    (tensorChartComponent_tsupport_subset_chartPouKernel
      (I := I) (M := M) g r s S α Idx Jdx).trans
      (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
  have hΩ_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) α
  have hp_one : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have hu_W1 : MemWkp (d := Module.finrank ℝ E) 1 2 u
      (chartTargetEuclid (I := I) (M := M) α) :=
    MemWkp_of_smooth_compactSupport (d := Module.finrank ℝ E) hΩ_open
      hu_smooth hu_cpt hu_tsupp hp_one 1
  have hu_W1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2 u
      (chartTargetEuclid (I := I) (M := M) α) :=
    MemWkp.one_iff_memW1p.mp hu_W1
  have h_ae := chosenWeakPartial_smooth_ae_eq (d := Module.finrank ℝ E)
    hp_one hΩ_open hu_smooth hu_W1p k
  rw [chartL2Measure]
  refine h_ae.trans (Filter.EventuallyEq.of_eq ?_)
  funext y; rw [euclidPartial_def]

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma coeFn_finsetSum_lp
    (α : M) {ι : Type*} (s : Finset ι)
    (G : ι → Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
    (((∑ a ∈ s, G a) : Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
        EuclN → ℝ)
      =ᵐ[chartL2Measure (I := I) (M := M) α]
      fun y => ∑ a ∈ s, ((G a : EuclN → ℝ) y) := by
  classical
  induction s using Finset.induction with
  | empty =>
      simp only [Finset.sum_empty]
      exact Lp.coeFn_zero _ _ _
  | insert a t ha ih =>
      rw [Finset.sum_insert ha]
      refine (Lp.coeFn_add (G a) (∑ b ∈ t, G b)).trans ?_
      filter_upwards [ih] with y hy
      rw [Pi.add_apply, hy, Finset.sum_insert ha]

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma coeFn_finsetSum_toLp
    (α : M) {ι : Type*} (s : Finset ι)
    {f : ι → EuclN → ℝ}
    (hf : ∀ a : ι, MemLp (f a) 2 (chartL2Measure (I := I) (M := M) α)) :
    (((∑ a ∈ s, (hf a).toLp (f a)) :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ)
      =ᵐ[chartL2Measure (I := I) (M := M) α]
      fun y => ∑ a ∈ s, f a y := by
  classical
  refine (coeFn_finsetSum_lp (I := I) (M := M) α s
    (fun a => (hf a).toLp (f a))).trans ?_
  induction s using Finset.induction with
  | empty => simp
  | insert a t ha ih =>
      filter_upwards [ih, MemLp.coeFn_toLp (hf a)] with y hy hya
      rw [Finset.sum_insert ha, Finset.sum_insert ha, hya, hy]

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma toLp_finsetSum_congr
    (α : M) {ι : Type*} (s : Finset ι)
    {f : ι → EuclN → ℝ}
    (hf : ∀ a : ι, MemLp (f a) 2 (chartL2Measure (I := I) (M := M) α))
    {F : EuclN → ℝ}
    (hF : MemLp F 2 (chartL2Measure (I := I) (M := M) α))
    (hFeq : F =ᵐ[chartL2Measure (I := I) (M := M) α]
      fun y => ∑ a ∈ s, f a y) :
    hF.toLp F = ∑ a ∈ s, (hf a).toLp (f a) := by
  classical
  apply Lp.ext
  exact (MemLp.coeFn_toLp hF).trans
    (hFeq.trans (coeFn_finsetSum_toLp (I := I) (M := M) α s hf).symm)

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma tendsto_toLp_finsetSum
    (α : M) {ι : Type*} (s : Finset ι)
    {f : ι → ℕ → EuclN → ℝ} {flim : ι → EuclN → ℝ}
    (hf : ∀ (a : ι) (n : ℕ),
      MemLp (f a n) 2 (chartL2Measure (I := I) (M := M) α))
    (hflim : ∀ a : ι, MemLp (flim a) 2 (chartL2Measure (I := I) (M := M) α))
    (h_tendsto : ∀ a : ι,
      Filter.Tendsto (fun n => (hf a n).toLp (f a n)) atTop
        (𝓝 ((hflim a).toLp (flim a))))
    {Fn : ℕ → EuclN → ℝ} {Flim : EuclN → ℝ}
    (hFn : ∀ n : ℕ, MemLp (Fn n) 2 (chartL2Measure (I := I) (M := M) α))
    (hFlim : MemLp Flim 2 (chartL2Measure (I := I) (M := M) α))
    (hFn_eq : ∀ n : ℕ, Fn n =ᵐ[chartL2Measure (I := I) (M := M) α]
      fun y => ∑ a ∈ s, f a n y)
    (hFlim_eq : Flim =ᵐ[chartL2Measure (I := I) (M := M) α]
      fun y => ∑ a ∈ s, flim a y) :
    Filter.Tendsto (fun n => (hFn n).toLp (Fn n)) atTop
      (𝓝 (hFlim.toLp Flim)) := by
  classical
  have h_n : ∀ n : ℕ,
      (hFn n).toLp (Fn n) =
        ∑ a ∈ s, (hf a n).toLp (f a n) :=
    fun n => toLp_finsetSum_congr (I := I) (M := M) α s
      (fun a => hf a n) (hFn n) (hFn_eq n)
  have h_lim :
      hFlim.toLp Flim = ∑ a ∈ s, (hflim a).toLp (flim a) :=
    toLp_finsetSum_congr (I := I) (M := M) α s hflim hFlim hFlim_eq
  rw [show (fun n => (hFn n).toLp (Fn n)) =
      (fun n => ∑ a ∈ s, (hf a n).toLp (f a n)) from funext h_n, h_lim]
  exact tendsto_finset_sum s (fun a _ => h_tendsto a)

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma memLp_indicatorFactor_mul_lp
    (α : M) {c : EuclN → ℝ}
    (hc : ContDiffOn ℝ ∞ c (chartTargetEuclid (I := I) (M := M) α))
    (G : Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
    MemLp
      (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α) c y *
        (G : EuclN → ℝ) y) 2 (chartL2Measure (I := I) (M := M) α) := by
  classical
  obtain ⟨C, hC_nn, hC⟩ := exists_bound_on_chartPouKernel (I := I) (M := M) α hc
  have hci_bd : ∀ y : EuclN,
      ‖Set.indicator (chartPouKernel (I := I) (M := M) α) c y‖ ≤ C := by
    intro y
    by_cases hy : y ∈ chartPouKernel (I := I) (M := M) α
    · rw [Set.indicator_of_mem hy]; exact hC y hy
    · rw [Set.indicator_of_notMem hy, norm_zero]; exact hC_nn
  exact memLp_bdd_mul (I := I) (M := M) α hC_nn hci_bd
    (aestronglyMeasurable_indicator_mul (I := I) (M := M) α hc) (Lp.memLp G)

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma tendsto_sumToLp
    (α : M) {ι : Type*} [Fintype ι]
    {f : ι → ℕ → EuclN → ℝ} {flim : ι → EuclN → ℝ}
    (hf : ∀ (a : ι) (n : ℕ),
      MemLp (f a n) 2 (chartL2Measure (I := I) (M := M) α))
    (hflim : ∀ a : ι, MemLp (flim a) 2 (chartL2Measure (I := I) (M := M) α))
    (h_tendsto : ∀ a : ι,
      Filter.Tendsto (fun n => (hf a n).toLp (f a n)) atTop
        (𝓝 ((hflim a).toLp (flim a)))) :
    Filter.Tendsto
      (fun n => (memLp_finset_sum (μ := chartL2Measure (I := I) (M := M) α)
        Finset.univ (fun a _ => hf a n)).toLp (fun y => ∑ a, f a n y))
      atTop
      (𝓝 ((memLp_finset_sum (μ := chartL2Measure (I := I) (M := M) α)
        Finset.univ (fun a _ => hflim a)).toLp (fun y => ∑ a, flim a y))) :=
  tendsto_toLp_finsetSum (I := I) (M := M) α Finset.univ hf hflim h_tendsto
    (fun n => memLp_finset_sum (μ := chartL2Measure (I := I) (M := M) α)
      Finset.univ (fun a _ => hf a n))
    (memLp_finset_sum (μ := chartL2Measure (I := I) (M := M) α)
      Finset.univ (fun a _ => hflim a))
    (fun _ => Filter.EventuallyEq.rfl) Filter.EventuallyEq.rfl

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
lemma euclidPartial_finsetSum
    (l : Fin (Module.finrank ℝ E)) {ι : Type*} (s : Finset ι)
    {f : ι → EuclN → ℝ} {y : EuclN}
    (hf : ∀ a ∈ s, DifferentiableAt ℝ (f a) y) :
    euclidPartial (E := E) l (fun z => ∑ a ∈ s, f a z) y =
      ∑ a ∈ s, euclidPartial (E := E) l (f a) y := by
  classical
  rw [euclidPartial_def, fderiv_fun_sum hf, ContinuousLinearMap.sum_apply]
  exact Finset.sum_congr rfl (fun a _ => by rw [euclidPartial_def])

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma tendsto_sum4
    (α : M) {κ₁ κ₂ κ₃ κ₄ : Type*}
    [Fintype κ₁] [Fintype κ₂] [Fintype κ₃] [Fintype κ₄]
    {f : κ₁ → κ₂ → κ₃ → κ₄ → ℕ → EuclN → ℝ}
    {flim : κ₁ → κ₂ → κ₃ → κ₄ → EuclN → ℝ}
    (hf : ∀ (a : κ₁) (b : κ₂) (c : κ₃) (d : κ₄) (n : ℕ),
      MemLp (f a b c d n) 2 (chartL2Measure (I := I) (M := M) α))
    (hflim : ∀ (a : κ₁) (b : κ₂) (c : κ₃) (d : κ₄),
      MemLp (flim a b c d) 2 (chartL2Measure (I := I) (M := M) α))
    (h_tendsto : ∀ (a : κ₁) (b : κ₂) (c : κ₃) (d : κ₄),
      Filter.Tendsto (fun n => (hf a b c d n).toLp (f a b c d n)) atTop
        (𝓝 ((hflim a b c d).toLp (flim a b c d)))) :
    Filter.Tendsto
      (fun n => (memLp_finset_sum (μ := chartL2Measure (I := I) (M := M) α)
          Finset.univ (fun a _ => memLp_finset_sum Finset.univ
            (fun b _ => memLp_finset_sum Finset.univ
              (fun c _ => memLp_finset_sum Finset.univ
                (fun d _ => hf a b c d n))))).toLp
        (fun y => ∑ a, ∑ b, ∑ c, ∑ d, f a b c d n y))
      atTop
      (𝓝 ((memLp_finset_sum (μ := chartL2Measure (I := I) (M := M) α)
          Finset.univ (fun a _ => memLp_finset_sum Finset.univ
            (fun b _ => memLp_finset_sum Finset.univ
              (fun c _ => memLp_finset_sum Finset.univ
                (fun d _ => hflim a b c d))))).toLp
        (fun y => ∑ a, ∑ b, ∑ c, ∑ d, flim a b c d y))) :=
  tendsto_sumToLp (I := I) (M := M) α
    (f := fun a => fun n y => ∑ b, ∑ c, ∑ d, f a b c d n y)
    (flim := fun a => fun y => ∑ b, ∑ c, ∑ d, flim a b c d y)
    (fun a n => memLp_finset_sum Finset.univ
      (fun b _ => memLp_finset_sum Finset.univ
        (fun c _ => memLp_finset_sum Finset.univ (fun d _ => hf a b c d n))))
    (fun a => memLp_finset_sum Finset.univ
      (fun b _ => memLp_finset_sum Finset.univ
        (fun c _ => memLp_finset_sum Finset.univ (fun d _ => hflim a b c d))))
    (fun a => tendsto_sumToLp (I := I) (M := M) α
      (f := fun b => fun n y => ∑ c, ∑ d, f a b c d n y)
      (flim := fun b => fun y => ∑ c, ∑ d, flim a b c d y)
      (fun b n => memLp_finset_sum Finset.univ
        (fun c _ => memLp_finset_sum Finset.univ (fun d _ => hf a b c d n)))
      (fun b => memLp_finset_sum Finset.univ
        (fun c _ => memLp_finset_sum Finset.univ (fun d _ => hflim a b c d)))
      (fun b => tendsto_sumToLp (I := I) (M := M) α
        (f := fun c => fun n y => ∑ d, f a b c d n y)
        (flim := fun c => fun y => ∑ d, flim a b c d y)
        (fun c n => memLp_finset_sum Finset.univ (fun d _ => hf a b c d n))
        (fun c => memLp_finset_sum Finset.univ (fun d _ => hflim a b c d))
        (fun c => tendsto_sumToLp (I := I) (M := M) α
          (hf := fun d n => hf a b c d n) (hflim := fun d => hflim a b c d)
          (h_tendsto a b c))))

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma tendsto_sum5
    (α : M) {κ₁ κ₂ κ₃ κ₄ κ₅ : Type*}
    [Fintype κ₁] [Fintype κ₂] [Fintype κ₃] [Fintype κ₄] [Fintype κ₅]
    {f : κ₁ → κ₂ → κ₃ → κ₄ → κ₅ → ℕ → EuclN → ℝ}
    {flim : κ₁ → κ₂ → κ₃ → κ₄ → κ₅ → EuclN → ℝ}
    (hf : ∀ (a : κ₁) (b : κ₂) (c : κ₃) (d : κ₄) (e : κ₅) (n : ℕ),
      MemLp (f a b c d e n) 2 (chartL2Measure (I := I) (M := M) α))
    (hflim : ∀ (a : κ₁) (b : κ₂) (c : κ₃) (d : κ₄) (e : κ₅),
      MemLp (flim a b c d e) 2 (chartL2Measure (I := I) (M := M) α))
    (h_tendsto : ∀ (a : κ₁) (b : κ₂) (c : κ₃) (d : κ₄) (e : κ₅),
      Filter.Tendsto (fun n => (hf a b c d e n).toLp (f a b c d e n)) atTop
        (𝓝 ((hflim a b c d e).toLp (flim a b c d e)))) :
    Filter.Tendsto
      (fun n => (memLp_finset_sum (μ := chartL2Measure (I := I) (M := M) α)
          Finset.univ (fun a _ => memLp_finset_sum Finset.univ
            (fun b _ => memLp_finset_sum Finset.univ
              (fun c _ => memLp_finset_sum Finset.univ
                (fun d _ => memLp_finset_sum Finset.univ
                  (fun e _ => hf a b c d e n)))))).toLp
        (fun y => ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, f a b c d e n y))
      atTop
      (𝓝 ((memLp_finset_sum (μ := chartL2Measure (I := I) (M := M) α)
          Finset.univ (fun a _ => memLp_finset_sum Finset.univ
            (fun b _ => memLp_finset_sum Finset.univ
              (fun c _ => memLp_finset_sum Finset.univ
                (fun d _ => memLp_finset_sum Finset.univ
                  (fun e _ => hflim a b c d e)))))).toLp
        (fun y => ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, flim a b c d e y))) :=
  tendsto_sumToLp (I := I) (M := M) α
    (f := fun a => fun n y => ∑ b, ∑ c, ∑ d, ∑ e, f a b c d e n y)
    (flim := fun a => fun y => ∑ b, ∑ c, ∑ d, ∑ e, flim a b c d e y)
    (fun a n => memLp_finset_sum Finset.univ
      (fun b _ => memLp_finset_sum Finset.univ
        (fun c _ => memLp_finset_sum Finset.univ
          (fun d _ => memLp_finset_sum Finset.univ
            (fun e _ => hf a b c d e n)))))
    (fun a => memLp_finset_sum Finset.univ
      (fun b _ => memLp_finset_sum Finset.univ
        (fun c _ => memLp_finset_sum Finset.univ
          (fun d _ => memLp_finset_sum Finset.univ
            (fun e _ => hflim a b c d e)))))
    (fun a => tendsto_sum4 (I := I) (M := M) α
      (f := fun b c d e n => f a b c d e n)
      (flim := fun b c d e => flim a b c d e)
      (fun b c d e n => hf a b c d e n)
      (fun b c d e => hflim a b c d e)
      (fun b c d e => h_tendsto a b c d e))

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
lemma differentiableAt_of_contDiffOn_chartTarget
    (α : M) {c : EuclN → ℝ}
    (hc : ContDiffOn ℝ ∞ c (chartTargetEuclid (I := I) (M := M) α))
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    DifferentiableAt ℝ c y := by
  have hopen : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) α
  exact (hc.contDiffAt (hopen.mem_nhds hy)).differentiableAt (by simp)

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
lemma differentiableAt_tensorChartComponent
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) (y : EuclN) :
    DifferentiableAt ℝ
      (tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx) y :=
  ((tensorChartComponent_contDiff' (I := I) (M := M) g r s S α Idx Jdx).differentiable
    (by simp)).differentiableAt

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma toLp_add_eq
    (α : M) {f₁ f₂ F : EuclN → ℝ}
    (hf₁ : MemLp f₁ 2 (chartL2Measure (I := I) (M := M) α))
    (hf₂ : MemLp f₂ 2 (chartL2Measure (I := I) (M := M) α))
    (hF : MemLp F 2 (chartL2Measure (I := I) (M := M) α))
    (hFeq : F =ᵐ[chartL2Measure (I := I) (M := M) α]
      fun y => f₁ y + f₂ y) :
    hF.toLp F = hf₁.toLp f₁ + hf₂.toLp f₂ := by
  classical
  apply Lp.ext
  refine (MemLp.coeFn_toLp hF).trans (hFeq.trans ?_)
  refine Filter.EventuallyEq.symm ?_
  refine (Lp.coeFn_add (hf₁.toLp f₁) (hf₂.toLp f₂)).trans ?_
  filter_upwards [MemLp.coeFn_toLp hf₁, MemLp.coeFn_toLp hf₂] with y hy₁ hy₂
  rw [Pi.add_apply, hy₁, hy₂]

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
