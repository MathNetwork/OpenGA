import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Iterated.EigenvectorIteratedRegularityHigher
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Iterated.EigenvectorIteratedNirenbergWeakenedQuant
import DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolevSpace.IteratedSobolevQuant

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Sobolev.Chart
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open DifferentialGeometry.Analysis.Sobolev.Euclidean

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

omit [CompleteSpace E] in
theorem eigenvectorChartIteratedPartial_wkpNorm_succ_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (K j : ℕ)
    (dirs : Fin j → Fin (Module.finrank ℝ E))
    (h_w1p :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) 1 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ j dirs)
        (chartTargetEuclid (I := I) (M := M) α))
    (h_succ :
      ∀ a : Fin (Module.finrank ℝ E),
        DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) (K + 1) 2
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ (j + 1) (Fin.snoc dirs a))
          (chartTargetEuclid (I := I) (M := M) α)) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (K + 2) 2
      (eigenvectorChartIteratedPartial (I := I) (M := M)
        g r s i α P₀ j dirs)
      (chartTargetEuclid (I := I) (M := M) α)
    ∧ DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) (K + 2) 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ j dirs)
        (chartTargetEuclid (I := I) (M := M) α)
      ≤ DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) 1 2
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ j dirs)
          (chartTargetEuclid (I := I) (M := M) α)
        + ∑ a : Fin (Module.finrank ℝ E),
            DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
              (d := Module.finrank ℝ E) (K + 1) 2
              (eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s i α P₀ (j + 1) (Fin.snoc dirs a))
              (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have h_succ_eq : ∀ a : Fin (Module.finrank ℝ E),
      eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ (j + 1) (Fin.snoc dirs a) =
        DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          (d := Module.finrank ℝ E) 2 a
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ j dirs) Ω := by
    intro a
    rw [eigenvectorChartIteratedPartial_succ]
    have h_last : (Fin.snoc dirs a :
        Fin (j + 1) → Fin (Module.finrank ℝ E)) (Fin.last j) = a :=
      Fin.snoc_last _ _
    have h_init : Fin.init (Fin.snoc dirs a :
        Fin (j + 1) → Fin (Module.finrank ℝ E)) = dirs := Fin.init_snoc _ _
    rw [h_last, h_init]
  have h_mem :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) (K + 2) 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ j dirs)
        (chartTargetEuclid (I := I) (M := M) α) := by
    rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_succ]
    refine ⟨?_, fun a => ?_⟩
    · rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.one_iff_memW1p]
        at h_w1p
      exact h_w1p
    · have h_next := h_succ a
      rw [h_succ_eq a] at h_next
      exact h_next
  refine ⟨h_mem, ?_⟩
  have h_rec := wkpNorm_succ_le (d := Module.finrank ℝ E)
    (K + 1) 2 Ω
    (eigenvectorChartIteratedPartial (I := I) (M := M)
      g r s i α P₀ j dirs)
  have h_idx : K + 1 + 1 = K + 2 := by ring
  rw [h_idx] at h_rec
  refine h_rec.trans (add_le_add ?_ ?_)
  · exact eLpNorm_le_wkpNorm (d := Module.finrank ℝ E) 1 2 Ω
      (eigenvectorChartIteratedPartial (I := I) (M := M)
        g r s i α P₀ j dirs)
  · refine Finset.sum_le_sum (fun a _ => ?_)
    rw [h_succ_eq a]

omit [CompleteSpace E] in
theorem eigenvectorChartIteratedPartial_wkpNorm_le_of_memWkp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (m : ℕ) :
    ∀ (k : ℕ),
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) (k + m) 2
        (eigenvectorChartComponentFun (I := I) (M := M) g r s i α P₀)
        (chartTargetEuclid (I := I) (M := M) α) →
      ∀ (dirs : Fin m → Fin (Module.finrank ℝ E)),
        DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) k 2
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ m dirs)
          (chartTargetEuclid (I := I) (M := M) α)
        ∧ DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
            (d := Module.finrank ℝ E) k 2
            (eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s i α P₀ m dirs)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
              (d := Module.finrank ℝ E) (k + m) 2
              (eigenvectorChartComponentFun (I := I) (M := M)
                g r s i α P₀)
              (chartTargetEuclid (I := I) (M := M) α) := by
  induction m with
  | zero =>
      intro k h_parent _dirs
      refine ⟨?_, ?_⟩
      · simpa [eigenvectorChartIteratedPartial_zero] using h_parent
      · rw [eigenvectorChartIteratedPartial_zero, Nat.add_zero]
  | succ m ih =>
      intro k h_parent dirs
      set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
      have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
      have h_parent' :
          DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
            (d := Module.finrank ℝ E) ((k + 1) + m) 2
            (eigenvectorChartComponentFun (I := I) (M := M)
              g r s i α P₀)
            (chartTargetEuclid (I := I) (M := M) α) := by
        have h_eq : (k + 1) + m = k + (m + 1) := by ring
        rw [h_eq]
        exact h_parent
      obtain ⟨h_inner_mem, h_inner_norm⟩ :=
        ih (k + 1) h_parent' (Fin.init dirs)
      have h_unfold :
          eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s i α P₀ (m + 1) dirs =
            DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
              (d := Module.finrank ℝ E) 2 (dirs (Fin.last m))
              (eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s i α P₀ m (Fin.init dirs)) Ω :=
        eigenvectorChartIteratedPartial_succ
          g r s i α P₀ m dirs
      refine ⟨?_, ?_⟩
      · rw [h_unfold]
        exact h_inner_mem.chosenWeakPartial_mem (dirs (Fin.last m))
      · rw [h_unfold]
        have h_peel := wkpNorm_chosenWeakPartial_le (d := Module.finrank ℝ E)
          k (p := 2) hΩ_open
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ m (Fin.init dirs)) (dirs (Fin.last m))
        refine h_peel.trans ?_
        have h_eq : (k + 1) + m = k + (m + 1) := by ring
        rw [h_eq] at h_inner_norm
        exact h_inner_norm

omit [CompleteSpace E] in
theorem eigenvectorChartIteratedPartial_wkpNorm_one_two_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (dirs : Fin m → Fin (Module.finrank ℝ E))
    (h_parent :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) (m + 1) 2
        (eigenvectorChartComponentFun (I := I) (M := M) g r s i α P₀)
        (chartTargetEuclid (I := I) (M := M) α)) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 1 2
      (eigenvectorChartIteratedPartial (I := I) (M := M)
        g r s i α P₀ m dirs)
      (chartTargetEuclid (I := I) (M := M) α)
    ∧ DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) 1 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ m dirs)
        (chartTargetEuclid (I := I) (M := M) α)
      ≤ DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) (m + 1) 2
          (eigenvectorChartComponentFun (I := I) (M := M) g r s i α P₀)
          (chartTargetEuclid (I := I) (M := M) α) := by
  have h_parent' :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) (1 + m) 2
        (eigenvectorChartComponentFun (I := I) (M := M) g r s i α P₀)
        (chartTargetEuclid (I := I) (M := M) α) := by
    have h_eq : 1 + m = m + 1 := Nat.add_comm 1 m
    rw [h_eq]
    exact h_parent
  obtain ⟨h_mem, h_norm⟩ :=
    eigenvectorChartIteratedPartial_wkpNorm_le_of_memWkp
      (I := I) (M := M) g r s i α P₀ m 1 h_parent' dirs
  refine ⟨h_mem, ?_⟩
  have h_eq : 1 + m = m + 1 := Nat.add_comm 1 m
  rw [h_eq] at h_norm
  exact h_norm

def eigenvectorIteratedW1Aggregate
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ) : ℝ≥0∞ :=
  ∑ j ∈ Finset.range (m + 1),
    ∑ idx : Fin j → Fin (Module.finrank ℝ E),
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) 1 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ j idx)
        (chartTargetEuclid (I := I) (M := M) α)

def eigenvectorIteratedW2Aggregate
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ) : ℝ≥0∞ :=
  ∑ idx : Fin m → Fin (Module.finrank ℝ E),
    DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
      (d := Module.finrank ℝ E) 2 2
      (eigenvectorChartIteratedPartial (I := I) (M := M)
        g r s i α P₀ m idx)
      (chartTargetEuclid (I := I) (M := M) α)

omit [CompleteSpace E] in
private lemma wkpNorm_one_le_eigenvectorIteratedW1Aggregate
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) {m j : ℕ} (hj : j ≤ m)
    (dirs : Fin j → Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) 1 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ j dirs)
        (chartTargetEuclid (I := I) (M := M) α)
      ≤ eigenvectorIteratedW1Aggregate (I := I) (M := M)
          g r s i α P₀ m := by
  classical
  unfold eigenvectorIteratedW1Aggregate
  have hj_mem : j ∈ Finset.range (m + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le hj)
  refine le_trans ?_ (Finset.single_le_sum
    (f := fun j' => ∑ idx : Fin j' → Fin (Module.finrank ℝ E),
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) 1 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ j' idx)
        (chartTargetEuclid (I := I) (M := M) α))
    (s := Finset.range (m + 1)) (fun _ _ => zero_le _) hj_mem)
  exact Finset.single_le_sum
    (f := fun idx : Fin j → Fin (Module.finrank ℝ E) =>
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) 1 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ j idx)
        (chartTargetEuclid (I := I) (M := M) α))
    (s := Finset.univ) (fun _ _ => zero_le _) (Finset.mem_univ dirs)

omit [CompleteSpace E] in
private lemma wkpNorm_two_le_eigenvectorIteratedW2Aggregate
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) {m : ℕ}
    (dirs : Fin m → Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) 2 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ m dirs)
        (chartTargetEuclid (I := I) (M := M) α)
      ≤ eigenvectorIteratedW2Aggregate (I := I) (M := M)
          g r s i α P₀ m := by
  classical
  unfold eigenvectorIteratedW2Aggregate
  exact Finset.single_le_sum
    (f := fun idx : Fin m → Fin (Module.finrank ℝ E) =>
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) 2 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ m idx)
        (chartTargetEuclid (I := I) (M := M) α))
    (fun _ _ => zero_le _) (Finset.mem_univ dirs)

omit [CompleteSpace E] in
private theorem eigenvectorIteratedPartial_wkpNorm_gapInduction
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (h_intermediate_w1p :
      ∀ (j : ℕ), j ≤ m → ∀ (idx : Fin j → Fin (Module.finrank ℝ E)),
        DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) 1 2
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ j idx)
          (chartTargetEuclid (I := I) (M := M) α))
    (h_top_memWkp_two :
      ∀ (idx : Fin m → Fin (Module.finrank ℝ E)),
        DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) 2 2
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ m idx)
          (chartTargetEuclid (I := I) (M := M) α)) :
    ∀ (gap j : ℕ), j + gap = m →
      ∀ (dirs : Fin j → Fin (Module.finrank ℝ E)),
        DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) (gap + 2) 2
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ j dirs)
          (chartTargetEuclid (I := I) (M := M) α)
        ∧ DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
            (d := Module.finrank ℝ E) (gap + 2) 2
            (eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s i α P₀ j dirs)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ((Module.finrank ℝ E : ℝ≥0∞) + 1) ^ gap *
              (eigenvectorIteratedW1Aggregate (I := I) (M := M)
                  g r s i α P₀ m
                + eigenvectorIteratedW2Aggregate (I := I) (M := M)
                  g r s i α P₀ m) := by
  classical
  intro gap
  induction gap with
  | zero =>
      intro j hj dirs
      subst hj
      simp only [Nat.add_zero] at *
      refine ⟨h_top_memWkp_two dirs, ?_⟩
      have h_single :
          DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
              (d := Module.finrank ℝ E) 2 2
              (eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s i α P₀ j dirs)
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ eigenvectorIteratedW2Aggregate (I := I) (M := M)
                g r s i α P₀ j :=
        wkpNorm_two_le_eigenvectorIteratedW2Aggregate
          (I := I) (M := M) g r s i α P₀ dirs
      refine h_single.trans ?_
      rw [pow_zero, one_mul]
      exact le_add_self
  | succ gap ih =>
      intro j hj dirs
      have hj_le : j ≤ m := by omega
      have hj1_eq : (j + 1) + gap = m := by omega
      have h_w1p_dirs :
          DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
            (d := Module.finrank ℝ E) 1 2
            (eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s i α P₀ j dirs)
            (chartTargetEuclid (I := I) (M := M) α) :=
        h_intermediate_w1p j hj_le dirs
      have h_ih_snoc : ∀ a : Fin (Module.finrank ℝ E),
          DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
            (d := Module.finrank ℝ E) (gap + 2) 2
            (eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s i α P₀ (j + 1) (Fin.snoc dirs a))
            (chartTargetEuclid (I := I) (M := M) α)
          ∧ DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
              (d := Module.finrank ℝ E) (gap + 2) 2
              (eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s i α P₀ (j + 1) (Fin.snoc dirs a))
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ((Module.finrank ℝ E : ℝ≥0∞) + 1) ^ gap *
                (eigenvectorIteratedW1Aggregate (I := I) (M := M)
                    g r s i α P₀ m
                  + eigenvectorIteratedW2Aggregate (I := I) (M := M)
                    g r s i α P₀ m) :=
        fun a => ih (j + 1) hj1_eq (Fin.snoc dirs a)
      have h_succ_mem : ∀ a : Fin (Module.finrank ℝ E),
          DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
            (d := Module.finrank ℝ E) (gap + 1 + 1) 2
            (eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s i α P₀ (j + 1) (Fin.snoc dirs a))
            (chartTargetEuclid (I := I) (M := M) α) := by
        intro a
        have h := (h_ih_snoc a).1
        have h_eq : gap + 1 + 1 = gap + 2 := by ring
        rw [h_eq]
        exact h
      obtain ⟨h_mem, h_norm_bound⟩ :=
        eigenvectorChartIteratedPartial_wkpNorm_succ_le
          (I := I) (M := M) g r s i α P₀ (gap + 1) j dirs
          h_w1p_dirs h_succ_mem
      refine ⟨h_mem, ?_⟩
      set W1 : ℝ≥0∞ :=
        eigenvectorIteratedW1Aggregate (I := I) (M := M)
          g r s i α P₀ m with hW1_def
      set W2 : ℝ≥0∞ :=
        eigenvectorIteratedW2Aggregate (I := I) (M := M)
          g r s i α P₀ m with hW2_def
      have h_w1_term :
          DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
              (d := Module.finrank ℝ E) 1 2
              (eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s i α P₀ j dirs)
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ((Module.finrank ℝ E : ℝ≥0∞) + 1) ^ gap * (W1 + W2) := by
        have h_single : DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
            (d := Module.finrank ℝ E) 1 2
            (eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s i α P₀ j dirs)
            (chartTargetEuclid (I := I) (M := M) α) ≤ W1 :=
          wkpNorm_one_le_eigenvectorIteratedW1Aggregate
            (I := I) (M := M) g r s i α P₀ hj_le dirs
        refine h_single.trans (le_trans (le_self_add (a := W1) (b := W2)) ?_)
        refine le_mul_of_one_le_left (zero_le _) ?_
        exact one_le_pow₀ (le_add_of_nonneg_left (zero_le _))
      have h_snoc_term : ∀ a : Fin (Module.finrank ℝ E),
          DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
              (d := Module.finrank ℝ E) (gap + 1 + 1) 2
              (eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s i α P₀ (j + 1) (Fin.snoc dirs a))
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ((Module.finrank ℝ E : ℝ≥0∞) + 1) ^ gap * (W1 + W2) := by
        intro a
        have h := (h_ih_snoc a).2
        have h_eq : gap + 1 + 1 = gap + 2 := by ring
        rw [h_eq]
        exact h
      have h_chain :
          DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
              (d := Module.finrank ℝ E) (gap + 1 + 2) 2
              (eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s i α P₀ j dirs)
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ((Module.finrank ℝ E : ℝ≥0∞) + 1) ^ gap * (W1 + W2)
              + ∑ _a : Fin (Module.finrank ℝ E),
                  ((Module.finrank ℝ E : ℝ≥0∞) + 1) ^ gap * (W1 + W2) := by
        refine h_norm_bound.trans (add_le_add h_w1_term ?_)
        exact Finset.sum_le_sum (fun a _ => h_snoc_term a)
      refine h_chain.trans (le_of_eq ?_)
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      rw [pow_succ]
      ring

omit [CompleteSpace E] in
theorem eigenvectorChartComponent_wkpNorm_m_plus_two_of_iterated_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (h_intermediate_w1p :
      ∀ (j : ℕ), j ≤ m → ∀ (idx : Fin j → Fin (Module.finrank ℝ E)),
        DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) 1 2
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ j idx)
          (chartTargetEuclid (I := I) (M := M) α))
    (h_top_memWkp_two :
      ∀ (idx : Fin m → Fin (Module.finrank ℝ E)),
        DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) 2 2
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ m idx)
          (chartTargetEuclid (I := I) (M := M) α)) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (m + 2) 2
      (eigenvectorChartComponentFun (I := I) (M := M) g r s i α P₀)
      (chartTargetEuclid (I := I) (M := M) α)
    ∧ ∃ C : ℝ, 0 < C ∧
        DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) (m + 2) 2
          (eigenvectorChartComponentFun (I := I) (M := M) g r s i α P₀)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal C *
            (eigenvectorIteratedW1Aggregate (I := I) (M := M)
                g r s i α P₀ m
              + eigenvectorIteratedW2Aggregate (I := I) (M := M)
                g r s i α P₀ m) := by
  classical
  have h_first :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) (m + 2) 2
        (eigenvectorChartComponentFun (I := I) (M := M) g r s i α P₀)
        (chartTargetEuclid (I := I) (M := M) α) :=
    eigenvectorChartComponent_memWkp_m_plus_two_of_iterated
      g r s i α P₀ m h_intermediate_w1p h_top_memWkp_two
  refine ⟨h_first, ?_⟩
  have h_gap := eigenvectorIteratedPartial_wkpNorm_gapInduction
    (I := I) (M := M) g r s i α P₀ m h_intermediate_w1p h_top_memWkp_two
    m 0 (by omega) Fin.elim0
  obtain ⟨_, h_gap_norm⟩ := h_gap
  rw [eigenvectorChartIteratedPartial_zero] at h_gap_norm
  refine ⟨((Module.finrank ℝ E : ℝ) + 1) ^ m, ?_, ?_⟩
  · have h_base : (0 : ℝ) < (Module.finrank ℝ E : ℝ) + 1 := by positivity
    exact pow_pos h_base m
  · have h_cast :
        ENNReal.ofReal (((Module.finrank ℝ E : ℝ) + 1) ^ m)
          = ((Module.finrank ℝ E : ℝ≥0∞) + 1) ^ m := by
      rw [ENNReal.ofReal_pow (by positivity)]
      congr 1
      rw [ENNReal.ofReal_add (by positivity) (by norm_num),
        ENNReal.ofReal_natCast, ENNReal.ofReal_one]
    rw [h_cast]
    exact h_gap_norm

omit [CompleteSpace E] in
theorem eigenvectorChartComponent_wkpNorm_m_plus_two_of_iterated_le_uniform
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
        (_h_intermediate_w1p :
          ∀ (j : ℕ), j ≤ m → ∀ (idx : Fin j → Fin (Module.finrank ℝ E)),
            DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
              (d := Module.finrank ℝ E) 1 2
              (eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s i α P₀ j idx)
              (chartTargetEuclid (I := I) (M := M) α))
        (_h_top_memWkp_two :
          ∀ (idx : Fin m → Fin (Module.finrank ℝ E)),
            DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
              (d := Module.finrank ℝ E) 2 2
              (eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s i α P₀ m idx)
              (chartTargetEuclid (I := I) (M := M) α)),
        DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) (m + 2) 2
          (eigenvectorChartComponentFun (I := I) (M := M) g r s i α P₀)
          (chartTargetEuclid (I := I) (M := M) α)
        ∧ DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
            (d := Module.finrank ℝ E) (m + 2) 2
            (eigenvectorChartComponentFun (I := I) (M := M) g r s i α P₀)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal C *
              (eigenvectorIteratedW1Aggregate (I := I) (M := M)
                  g r s i α P₀ m
                + eigenvectorIteratedW2Aggregate (I := I) (M := M)
                  g r s i α P₀ m) := by
  classical
  refine ⟨((Module.finrank ℝ E : ℝ) + 1) ^ m, ?_, ?_⟩
  · have h_base : (0 : ℝ) < (Module.finrank ℝ E : ℝ) + 1 := by positivity
    exact pow_pos h_base m
  intro i h_intermediate_w1p h_top_memWkp_two
  have h_first :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) (m + 2) 2
        (eigenvectorChartComponentFun (I := I) (M := M) g r s i α P₀)
        (chartTargetEuclid (I := I) (M := M) α) :=
    eigenvectorChartComponent_memWkp_m_plus_two_of_iterated
      g r s i α P₀ m h_intermediate_w1p h_top_memWkp_two
  refine ⟨h_first, ?_⟩
  have h_gap := eigenvectorIteratedPartial_wkpNorm_gapInduction
    (I := I) (M := M) g r s i α P₀ m h_intermediate_w1p h_top_memWkp_two
    m 0 (by omega) Fin.elim0
  obtain ⟨_, h_gap_norm⟩ := h_gap
  rw [eigenvectorChartIteratedPartial_zero] at h_gap_norm
  have h_cast :
      ENNReal.ofReal (((Module.finrank ℝ E : ℝ) + 1) ^ m)
        = ((Module.finrank ℝ E : ℝ≥0∞) + 1) ^ m := by
    rw [ENNReal.ofReal_pow (by positivity)]
    congr 1
    rw [ENNReal.ofReal_add (by positivity) (by norm_num),
      ENNReal.ofReal_natCast, ENNReal.ofReal_one]
  rw [h_cast]
  exact h_gap_norm

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
