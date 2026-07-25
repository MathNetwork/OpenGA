import DifferentialGeometry.Analysis.Sobolev.Chart.Defs
import DifferentialGeometry.Analysis.Sobolev.Chart.BanachCompleteness.Banach


noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Function
open scoped Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Chart

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def MemWkpChartGen [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (_g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (k : ℕ) (p : ℝ≥0∞)
    (ρ : SmoothPartitionOfUnity M I M Set.univ)
    (u : M → ℝ) : Prop :=
  ∀ α : M,
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E)
      k p
      (chartPushed (I := I) (M := M) ρ α u)
      (chartTargetEuclid (I := I) (M := M) α)

def wkpNormChartGen [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (_g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (k : ℕ) (p : ℝ≥0∞)
    (ρ : SmoothPartitionOfUnity M I M Set.univ)
    (u : M → ℝ) : ℝ≥0∞ :=
  ∑' α : M,
    DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
      (d := Module.finrank ℝ E)
      k p
      (chartPushed (I := I) (M := M) ρ α u)
      (chartTargetEuclid (I := I) (M := M) α)

theorem MemWkpChartGen_chartAtlasPOU
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (k : ℕ) (p : ℝ≥0∞) (u : M → ℝ) :
    MemWkpChartGen (I := I) (M := M) g k p
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) u ↔
      MemWkpChart (I := I) (M := M) g k p u := Iff.rfl

theorem wkpNormChartGen_chartAtlasPOU
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (k : ℕ) (p : ℝ≥0∞) (u : M → ℝ) :
    wkpNormChartGen (I := I) (M := M) g k p
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) u =
      wkpNormChart (I := I) (M := M) g k p u := rfl

omit [IsManifold I ∞ M] in
theorem chartPushed_congr_of_pointwise_eq
    (ρ ρ' : SmoothPartitionOfUnity M I M Set.univ)
    (h : ∀ α : M, ∀ x : M, (ρ α : C^∞⟮I, M; ℝ⟯) x = (ρ' α : C^∞⟮I, M; ℝ⟯) x)
    (α : M) (u : M → ℝ) :
    chartPushed (I := I) (M := M) ρ α u =
      chartPushed (I := I) (M := M) ρ' α u := by
  funext y
  unfold chartPushed
  rw [h α]

theorem wkpNormChartGen_congr_of_pointwise_eq
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (k : ℕ) (p : ℝ≥0∞)
    (ρ ρ' : SmoothPartitionOfUnity M I M Set.univ)
    (h : ∀ α : M, ∀ x : M, (ρ α : C^∞⟮I, M; ℝ⟯) x = (ρ' α : C^∞⟮I, M; ℝ⟯) x)
    (u : M → ℝ) :
    wkpNormChartGen (I := I) (M := M) g k p ρ u =
      wkpNormChartGen (I := I) (M := M) g k p ρ' u := by
  unfold wkpNormChartGen
  refine tsum_congr (fun α => ?_)
  rw [chartPushed_congr_of_pointwise_eq (I := I) (M := M) ρ ρ' h α u]

theorem MemWkpChartGen_congr_of_pointwise_eq
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {k : ℕ} {p : ℝ≥0∞}
    (ρ ρ' : SmoothPartitionOfUnity M I M Set.univ)
    (h : ∀ α : M, ∀ x : M, (ρ α : C^∞⟮I, M; ℝ⟯) x = (ρ' α : C^∞⟮I, M; ℝ⟯) x)
    (u : M → ℝ) :
    MemWkpChartGen (I := I) (M := M) g k p ρ u ↔
      MemWkpChartGen (I := I) (M := M) g k p ρ' u := by
  refine ⟨fun H α => ?_, fun H α => ?_⟩
  · have hcp := chartPushed_congr_of_pointwise_eq (I := I) (M := M) ρ ρ' h α u
    rw [← hcp]
    exact H α
  · have hcp := chartPushed_congr_of_pointwise_eq (I := I) (M := M) ρ ρ'
      h α u
    rw [hcp]
    exact H α

omit [IsManifold I ∞ M] in

theorem chartPushed_zero_gen
    (ρ : SmoothPartitionOfUnity M I M Set.univ) (α : M) :
    chartPushed (I := I) (M := M) ρ α (fun _ => (0 : ℝ)) =
      (fun _ => (0 : ℝ)) :=
  chartPushed_zero (I := I) (M := M) ρ α

theorem MemWkpChartGen_zero_fun
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (ρ : SmoothPartitionOfUnity M I M Set.univ) :
    MemWkpChartGen (I := I) (M := M) g k p ρ (fun _ : M => (0 : ℝ)) := by
  intro α
  rw [chartPushed_zero_gen]
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_zero_fun
    (d := Module.finrank ℝ E) hp (chartTargetEuclid_isOpen (I := I) (M := M) α)

theorem wkpNormChartGen_zero_fun
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (ρ : SmoothPartitionOfUnity M I M Set.univ) :
    wkpNormChartGen (I := I) (M := M) g k p ρ (fun _ : M => (0 : ℝ)) = 0 := by
  unfold wkpNormChartGen
  have hpt : ∀ α : M,
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) k p
        (chartPushed (I := I) (M := M) ρ α (fun _ : M => (0 : ℝ)))
        (chartTargetEuclid (I := I) (M := M) α) = 0 := by
    intro α
    rw [chartPushed_zero_gen]
    exact DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_zero_fun_zero
      (d := Module.finrank ℝ E) hp
      (chartTargetEuclid_isOpen (I := I) (M := M) α)
  rw [tsum_congr hpt]
  exact tsum_zero

omit [IsManifold I ∞ M] in

theorem chartPushed_add_gen
    (ρ : SmoothPartitionOfUnity M I M Set.univ) (α : M) (u v : M → ℝ) :
    chartPushed (I := I) (M := M) ρ α (fun x => u x + v x) =
      (fun y =>
        chartPushed (I := I) (M := M) ρ α u y +
          chartPushed (I := I) (M := M) ρ α v y) :=
  chartPushed_add (I := I) (M := M) ρ α u v

omit [IsManifold I ∞ M] in

theorem chartPushed_const_smul_gen
    (ρ : SmoothPartitionOfUnity M I M Set.univ) (α : M) (c : ℝ) (u : M → ℝ) :
    chartPushed (I := I) (M := M) ρ α (fun x => c * u x) =
      (fun y => c * chartPushed (I := I) (M := M) ρ α u y) :=
  chartPushed_const_smul (I := I) (M := M) ρ α c u

theorem MemWkpChartGen_add
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (ρ : SmoothPartitionOfUnity M I M Set.univ)
    {u v : M → ℝ}
    (hu : MemWkpChartGen (I := I) (M := M) g k p ρ u)
    (hv : MemWkpChartGen (I := I) (M := M) g k p ρ v) :
    MemWkpChartGen (I := I) (M := M) g k p ρ (fun x => u x + v x) := by
  intro α
  rw [chartPushed_add_gen]
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.add
    (d := Module.finrank ℝ E) hp
    (chartTargetEuclid_isOpen (I := I) (M := M) α)
    (hu α) (hv α)

theorem MemWkpChartGen_const_smul
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (ρ : SmoothPartitionOfUnity M I M Set.univ)
    (c : ℝ) {u : M → ℝ}
    (hu : MemWkpChartGen (I := I) (M := M) g k p ρ u) :
    MemWkpChartGen (I := I) (M := M) g k p ρ (fun x => c * u x) := by
  intro α
  rw [chartPushed_const_smul_gen]
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.const_smul
    (d := Module.finrank ℝ E) hp
    (chartTargetEuclid_isOpen (I := I) (M := M) α)
    (hu α) c

theorem MemWkpChartGen_neg
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (ρ : SmoothPartitionOfUnity M I M Set.univ)
    {u : M → ℝ}
    (hu : MemWkpChartGen (I := I) (M := M) g k p ρ u) :
    MemWkpChartGen (I := I) (M := M) g k p ρ (fun x => -u x) := by
  have h := MemWkpChartGen_const_smul (I := I) (M := M) g hp ρ (-1) hu
  have hEq : (fun x : M => (-1 : ℝ) * u x) = (fun x : M => -u x) := by
    funext x; ring
  rw [hEq] at h
  exact h

theorem MemWkpChartGen_sub
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (ρ : SmoothPartitionOfUnity M I M Set.univ)
    {u v : M → ℝ}
    (hu : MemWkpChartGen (I := I) (M := M) g k p ρ u)
    (hv : MemWkpChartGen (I := I) (M := M) g k p ρ v) :
    MemWkpChartGen (I := I) (M := M) g k p ρ (fun x => u x - v x) := by
  have hneg := MemWkpChartGen_neg (I := I) (M := M) g hp ρ hv
  have h := MemWkpChartGen_add (I := I) (M := M) g hp ρ hu hneg
  have hEq : (fun x : M => u x + -v x) = (fun x : M => u x - v x) := by
    funext x; ring
  rw [hEq] at h
  exact h

theorem wkpNormChartGen_add_le
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (ρ : SmoothPartitionOfUnity M I M Set.univ)
    {u v : M → ℝ}
    (hu : MemWkpChartGen (I := I) (M := M) g k p ρ u)
    (hv : MemWkpChartGen (I := I) (M := M) g k p ρ v) :
    wkpNormChartGen (I := I) (M := M) g k p ρ (fun x => u x + v x) ≤
      wkpNormChartGen (I := I) (M := M) g k p ρ u +
        wkpNormChartGen (I := I) (M := M) g k p ρ v := by
  unfold wkpNormChartGen
  rw [← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum ?_
  intro α
  rw [chartPushed_add_gen]
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_add_le
    (d := Module.finrank ℝ E) hp
    (chartTargetEuclid_isOpen (I := I) (M := M) α)
    (hu α) (hv α)

theorem wkpNormChartGen_const_smul
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (ρ : SmoothPartitionOfUnity M I M Set.univ)
    (c : ℝ) {u : M → ℝ}
    (hu : MemWkpChartGen (I := I) (M := M) g k p ρ u) :
    wkpNormChartGen (I := I) (M := M) g k p ρ (fun x => c * u x) =
      ‖c‖ₑ * wkpNormChartGen (I := I) (M := M) g k p ρ u := by
  unfold wkpNormChartGen
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr ?_
  intro α
  rw [chartPushed_const_smul_gen]
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_const_smul
    (d := Module.finrank ℝ E) hp
    (chartTargetEuclid_isOpen (I := I) (M := M) α)
    (hu α) c

theorem MemWkpChartGen.le_succ
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    {g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M}
    {k : ℕ} {p : ℝ≥0∞}
    {ρ : SmoothPartitionOfUnity M I M Set.univ}
    {u : M → ℝ}
    (h : MemWkpChartGen (I := I) (M := M) g (k + 1) p ρ u) :
    MemWkpChartGen (I := I) (M := M) g k p ρ u := by
  intro α
  exact (h α).le_succ

theorem MemWkpChartGen.le_of_le
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    {g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M}
    {k k' : ℕ} {p : ℝ≥0∞}
    {ρ : SmoothPartitionOfUnity M I M Set.univ}
    {u : M → ℝ}
    (hk : k ≤ k') (h : MemWkpChartGen (I := I) (M := M) g k' p ρ u) :
    MemWkpChartGen (I := I) (M := M) g k p ρ u := by
  intro α
  exact (h α).le_of_le hk

theorem wkpNormChartGen_lt_top_of_memWkpChartGen
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (ρ : SmoothPartitionOfUnity M I M Set.univ)
    {u : M → ℝ} (hu : MemWkpChartGen (I := I) (M := M) g k p ρ u) :
    wkpNormChartGen (I := I) (M := M) g k p ρ u < ⊤ := by
  classical
  unfold wkpNormChartGen
  set f : M → ℝ≥0∞ := fun α =>
    DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
      (d := Module.finrank ℝ E) k p
      (chartPushed (I := I) (M := M) ρ α u)
      (chartTargetEuclid (I := I) (M := M) α) with hf_def
  have hPOU_locFin : LocallyFinite
      (fun α : M => Function.support (ρ α : M → ℝ)) :=
    ρ.locallyFinite
  have hSupport_finite : {α : M | (Function.support (ρ α : M → ℝ)).Nonempty}.Finite :=
    hPOU_locFin.finite_nonempty_of_compact
  have hf_zero_off : ∀ α : M, (Function.support (ρ α : M → ℝ)) = ∅ →
        f α = 0 := by
    intro α hα
    have hρ_empty : ∀ x : M, (ρ α : M → ℝ) x = 0 := by
      intro x
      have : x ∉ Function.support (ρ α : M → ℝ) := by
        rw [hα]
        exact Set.notMem_empty x
      simpa [Function.mem_support] using this
    have hChartPushed_zero : chartPushed (I := I) (M := M) ρ α u =
        (fun _ => (0 : ℝ)) := by
      funext y
      unfold chartPushed
      rw [hρ_empty]
      ring
    change DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
      (d := Module.finrank ℝ E) k p
      (chartPushed (I := I) (M := M) ρ α u)
      (chartTargetEuclid (I := I) (M := M) α) = 0
    rw [hChartPushed_zero]
    exact DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_zero_fun_zero
      (d := Module.finrank ℝ E) hp
      (chartTargetEuclid_isOpen (I := I) (M := M) α)
  set S : Set M := {α : M | (Function.support (ρ α : M → ℝ)).Nonempty}
      with hS_def
  have hS_finite : S.Finite := hSupport_finite
  have htsum_eq : ∑' α : M, f α = ∑ α ∈ hS_finite.toFinset, f α := by
    rw [tsum_eq_sum]
    intro α hα
    have hαS : α ∉ S := by
      intro hαS
      apply hα
      exact (Set.Finite.mem_toFinset _).mpr hαS
    have hempty : (Function.support (ρ α : M → ℝ)) = ∅ := by
      have h_not_nonempty : ¬ (Function.support (ρ α : M → ℝ)).Nonempty := by
        intro hne
        exact hαS hne
      exact Set.not_nonempty_iff_eq_empty.mp h_not_nonempty
    exact hf_zero_off α hempty
  rw [htsum_eq]
  apply ENNReal.sum_lt_top.mpr
  intro α _
  rw [hf_def]
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_lt_top_of_memWkp
    (d := Module.finrank ℝ E) (hu α)

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem support_set_finite_of_compactSpace
    [CompactSpace M]
    (ρ : SmoothPartitionOfUnity M I M Set.univ) :
    {α : M | (Function.support (ρ α : M → ℝ)).Nonempty}.Finite :=
  ρ.locallyFinite.finite_nonempty_of_compact

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem fintsupport_finite
    (ρ : SmoothPartitionOfUnity M I M Set.univ) (x₀ : M) :
    {α : M | x₀ ∈ tsupport (ρ α : M → ℝ)}.Finite :=
  ρ.finite_tsupport x₀

omit [IsManifold I ∞ M] in

omit [FiniteDimensional ℝ E] in
theorem support_pou_mul_subset
    (ρ ρ' : SmoothPartitionOfUnity M I M Set.univ) (α β : M) :
    Function.support (fun x : M => (ρ α : M → ℝ) x * (ρ' β : M → ℝ) x) ⊆
      Function.support (ρ α : M → ℝ) ∩ Function.support (ρ' β : M → ℝ) := by
  intro x hx
  simp only [Function.mem_support] at hx
  refine ⟨?_, ?_⟩ <;> simp only [Function.mem_support] <;> intro h <;>
    apply hx <;> rw [h] <;> ring

omit [IsManifold I ∞ M] in

omit [FiniteDimensional ℝ E] in
theorem tsupport_pou_mul_subset
    (ρ ρ' : SmoothPartitionOfUnity M I M Set.univ) (α β : M) :
    tsupport (fun x : M => (ρ α : M → ℝ) x * (ρ' β : M → ℝ) x) ⊆
      tsupport (ρ α : M → ℝ) ∩ tsupport (ρ' β : M → ℝ) := by
  refine subset_inter ?_ ?_
  · refine closure_mono ?_
    intro x hx
    simp only [Function.mem_support] at hx
    simp only [Function.mem_support]
    intro h; exact hx (by rw [h]; ring)
  · refine closure_mono ?_
    intro x hx
    simp only [Function.mem_support] at hx
    simp only [Function.mem_support]
    intro h; exact hx (by rw [h]; ring)

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem tsupport_subset_chartAt_source
    (ρ : SmoothPartitionOfUnity M I M Set.univ)
    (hρ : ρ.IsSubordinate (fun α : M => (chartAt H α).source))
    (α : M) :
    tsupport (ρ α : M → ℝ) ⊆ (chartAt H α).source := hρ α

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem support_subset_chartAt_source
    (ρ : SmoothPartitionOfUnity M I M Set.univ)
    (hρ : ρ.IsSubordinate (fun α : M => (chartAt H α).source))
    (α : M) :
    Function.support (ρ α : M → ℝ) ⊆ (chartAt H α).source :=
  (subset_tsupport _).trans (tsupport_subset_chartAt_source ρ hρ α)

omit [IsManifold I ∞ M] in
theorem chartPushed_pointwise_bound
    (ρ : SmoothPartitionOfUnity M I M Set.univ) (α : M) (u : M → ℝ)
    (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    |chartPushed (I := I) (M := M) ρ α u y| ≤
      |u ((extChartAt I α).symm (toEuclidean.symm y))| := by
  unfold chartPushed
  rw [abs_mul]
  have hbound : |(ρ α : C^∞⟮I, M; ℝ⟯) ((extChartAt I α).symm (toEuclidean.symm y))| ≤ 1 := by
    rw [abs_of_nonneg (ρ.nonneg α _)]
    exact ρ.le_one α _
  have hu_nonneg : 0 ≤ |u ((extChartAt I α).symm (toEuclidean.symm y))| := abs_nonneg _
  calc
    |(ρ α : C^∞⟮I, M; ℝ⟯) ((extChartAt I α).symm (toEuclidean.symm y))| *
        |u ((extChartAt I α).symm (toEuclidean.symm y))|
      ≤ 1 * |u ((extChartAt I α).symm (toEuclidean.symm y))| :=
        mul_le_mul_of_nonneg_right hbound hu_nonneg
    _ = |u ((extChartAt I α).symm (toEuclidean.symm y))| := one_mul _

def wkpNormChartFin
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (_g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (k : ℕ) (p : ℝ≥0∞)
    (ρ : SmoothPartitionOfUnity M I M Set.univ)
    (u : M → ℝ) : ℝ≥0∞ :=
  ∑ α ∈ (support_set_finite_of_compactSpace (I := I) (M := M) ρ).toFinset,
    DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
      (d := Module.finrank ℝ E)
      k p
      (chartPushed (I := I) (M := M) ρ α u)
      (chartTargetEuclid (I := I) (M := M) α)

theorem wkpNormChartGen_eq_wkpNormChartFin
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (ρ : SmoothPartitionOfUnity M I M Set.univ)
    (u : M → ℝ) :
    wkpNormChartGen (I := I) (M := M) g k p ρ u =
      wkpNormChartFin (I := I) (M := M) g k p ρ u := by
  classical
  let f : M → ℝ≥0∞ := fun α =>
    DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
      (d := Module.finrank ℝ E) k p
      (chartPushed (I := I) (M := M) ρ α u)
      (chartTargetEuclid (I := I) (M := M) α)
  have hLHS : wkpNormChartGen (I := I) (M := M) g k p ρ u = ∑' α : M, f α := rfl
  have hRHS : wkpNormChartFin (I := I) (M := M) g k p ρ u =
      ∑ α ∈ (support_set_finite_of_compactSpace (I := I) (M := M) ρ).toFinset,
        f α := rfl
  rw [hLHS, hRHS]
  have hf_zero_off : ∀ α : M, (Function.support (ρ α : M → ℝ)) = ∅ →
        f α = 0 := by
    intro α hα
    have hρ_empty : ∀ x : M, (ρ α : M → ℝ) x = 0 := by
      intro x
      have : x ∉ Function.support (ρ α : M → ℝ) := by
        rw [hα]
        exact Set.notMem_empty x
      simpa [Function.mem_support] using this
    have hChartPushed_zero : chartPushed (I := I) (M := M) ρ α u =
        (fun _ => (0 : ℝ)) := by
      funext y
      unfold chartPushed
      rw [hρ_empty]
      ring
    change DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
      (d := Module.finrank ℝ E) k p
      (chartPushed (I := I) (M := M) ρ α u)
      (chartTargetEuclid (I := I) (M := M) α) = 0
    rw [hChartPushed_zero]
    exact DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_zero_fun_zero
      (d := Module.finrank ℝ E) hp
      (chartTargetEuclid_isOpen (I := I) (M := M) α)
  rw [tsum_eq_sum]
  intro α hα
  have hαS : α ∉ {α : M | (Function.support (ρ α : M → ℝ)).Nonempty} := by
    intro hαS
    apply hα
    exact (Set.Finite.mem_toFinset _).mpr hαS
  have hempty : (Function.support (ρ α : M → ℝ)) = ∅ := by
    have h_not_nonempty : ¬ (Function.support (ρ α : M → ℝ)).Nonempty := by
      intro hne
      exact hαS hne
    exact Set.not_nonempty_iff_eq_empty.mp h_not_nonempty
  exact hf_zero_off α hempty

def chartTransitionFinset
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (ρ : SmoothPartitionOfUnity M I M Set.univ) : Finset M :=
  (support_set_finite_of_compactSpace (I := I) (M := M) ρ).toFinset

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem mem_chartTransitionFinset_iff
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (ρ : SmoothPartitionOfUnity M I M Set.univ) (α : M) :
    α ∈ chartTransitionFinset (I := I) (M := M) ρ ↔
      (Function.support (ρ α : M → ℝ)).Nonempty := by
  unfold chartTransitionFinset
  rw [Set.Finite.mem_toFinset]
  rfl

omit [FiniteDimensional ℝ E] in
theorem chartAt_transition_hasFDerivWithinAt_overlap
    [I.Boundaryless] (α β : M) :
    ∀ y ∈ (extChartAt I α) ''
      ((chartAt H α).source ∩ (chartAt H β).source),
        HasFDerivWithinAt (extChartAt I β ∘ (extChartAt I α).symm)
          (tangentCoordChange I α β ((extChartAt I α).symm y))
          ((extChartAt I α) ''
            ((chartAt H α).source ∩ (chartAt H β).source)) y :=
  DifferentialGeometry.Integral.Measure.extChartAt_transition_hasFDerivWithinAt_on_overlap_image
    (I := I) α β Set.inter_subset_left Set.inter_subset_right

end Chart
end Sobolev
end Analysis
end DifferentialGeometry
