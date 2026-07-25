import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Iterated.EigenvectorIteratedDatum
import DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.TwiceDifferentiated.DerivedData


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
open DifferentialGeometry.Analysis.Laplacian.TwiceDerivedChartBilinearH1ComplData
open DifferentialGeometry.Analysis.Sobolev.Chart
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open DifferentialGeometry.Analysis.Sobolev.Euclidean

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

omit [CompleteSpace E] [CompactSpace M] [I.Boundaryless] [T2Space M]
  [SigmaCompactSpace M] in

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma fin_cons_last_succ
    {a : Fin (Module.finrank ℝ E)} {m : ℕ}
    (dirs : Fin (m + 1) → Fin (Module.finrank ℝ E)) :
    (Fin.cons a dirs : Fin (m + 2) → Fin (Module.finrank ℝ E))
        (Fin.last (m + 1)) = dirs (Fin.last m) := by
  have h : (Fin.last (m + 1) : Fin (m + 2)) = (Fin.last m).succ := by
    ext; simp [Fin.last]
  rw [h, Fin.cons_succ]

omit [CompleteSpace E] [CompactSpace M] [I.Boundaryless] [T2Space M]
  [SigmaCompactSpace M] in

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma fin_init_cons
    {a : Fin (Module.finrank ℝ E)} {m : ℕ}
    (dirs : Fin (m + 1) → Fin (Module.finrank ℝ E)) :
    Fin.init (Fin.cons a dirs : Fin (m + 2) → Fin (Module.finrank ℝ E)) =
      Fin.cons a (Fin.init dirs) := by
  funext k
  refine Fin.cases ?_ ?_ k
  · simp [Fin.init]
  · intro k
    simp [Fin.init, Fin.cons_succ]

omit [CompleteSpace E] in
theorem eigenvectorChartIteratedPartial_cons_eq_chosenWeakPartial_ae
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    ∀ (m : ℕ) (dirs : Fin m → Fin (Module.finrank ℝ E))
      (a : Fin (Module.finrank ℝ E)),
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) (m + 1) 2
        (eigenvectorChartComponentFun (I := I) (M := M) g r s i α P₀)
        (chartTargetEuclid (I := I) (M := M) α) →
      eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ (m + 1) (Fin.cons a dirs)
        =ᵐ[(volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      chosenWeakPartial' (d := Module.finrank ℝ E) 2 a
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ m dirs)
        (chartTargetEuclid (I := I) (M := M) α) := by
  intro m
  induction m with
  | zero =>
      intro dirs a _h_parent
      have h_lhs_eq :
          eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s i α P₀ 1 (Fin.cons a dirs) =
            chosenWeakPartial' (d := Module.finrank ℝ E) 2 a
              (eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s i α P₀ 0 dirs)
              (chartTargetEuclid (I := I) (M := M) α) := by
        rw [eigenvectorChartIteratedPartial_succ]
        have h_last : (Fin.cons a dirs : Fin 1 → _) (Fin.last 0) = a := rfl
        have h_init : Fin.init (Fin.cons a dirs : Fin 1 → _) = dirs := by
          funext k; exact (k.elim0)
        rw [h_last, h_init]
      exact Filter.EventuallyEq.of_eq h_lhs_eq
  | succ m ih =>
      intro dirs a h_parent
      classical
      set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
      have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
      have h_last : (Fin.cons a dirs : Fin (m + 2) → Fin (Module.finrank ℝ E))
          (Fin.last (m + 1)) = dirs (Fin.last m) := fin_cons_last_succ dirs
      have h_init : Fin.init (Fin.cons a dirs :
          Fin (m + 2) → Fin (Module.finrank ℝ E)) = Fin.cons a (Fin.init dirs) :=
        fin_init_cons dirs
      have h_lhs_unfold :
          eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s i α P₀ (m + 2) (Fin.cons a dirs) =
            chosenWeakPartial' (d := Module.finrank ℝ E) 2 (dirs (Fin.last m))
              (eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s i α P₀ (m + 1) (Fin.cons a (Fin.init dirs))) Ω := by
        rw [eigenvectorChartIteratedPartial_succ, h_last, h_init]
      have h_dirs_unfold :
          eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s i α P₀ (m + 1) dirs =
            chosenWeakPartial' (d := Module.finrank ℝ E) 2 (dirs (Fin.last m))
              (eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s i α P₀ m (Fin.init dirs)) Ω := by
        rw [eigenvectorChartIteratedPartial_succ]
      have h_parent_for_ih :
          DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
            (d := Module.finrank ℝ E) (m + 1) 2
            (eigenvectorChartComponentFun (I := I) (M := M)
              g r s i α P₀)
            Ω :=
        DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.le_of_le
          (by omega) h_parent
      have h_ih := ih (Fin.init dirs) a h_parent_for_ih
      have h_propagate :
          chosenWeakPartial' (d := Module.finrank ℝ E) 2 (dirs (Fin.last m))
              (eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s i α P₀ (m + 1) (Fin.cons a (Fin.init dirs))) Ω
            =ᵐ[(volume : Measure EuclN).restrict Ω]
          chosenWeakPartial' (d := Module.finrank ℝ E) 2 (dirs (Fin.last m))
            (chosenWeakPartial' (d := Module.finrank ℝ E) 2 a
              (eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s i α P₀ m (Fin.init dirs)) Ω) Ω :=
        chosenWeakPartial'_ae_congr (d := Module.finrank ℝ E)
          (p := 2) (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_ih (dirs (Fin.last m))
      have h_inner_memWkp_2_2 :
          DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
            (d := Module.finrank ℝ E) 2 2
            (eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s i α P₀ m (Fin.init dirs)) Ω := by
        have h_parent_2_m :
            DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
              (d := Module.finrank ℝ E) (2 + m) 2
              (eigenvectorChartComponentFun (I := I) (M := M)
                g r s i α P₀) Ω := by
          have h_eq : (2 : ℕ) + m = m + 2 := by ring
          rw [h_eq]; exact h_parent
        exact eigenvectorChartIteratedPartial_memWkp_of_memWkp
          (I := I) (M := M) g r s i α P₀ m 2 h_parent_2_m (Fin.init dirs)
      have h_swap :=
        chosenWeakPartial'_swap_ae_of_memWkp_two
          hΩ_open h_inner_memWkp_2_2 a (dirs (Fin.last m))
      have h_final :
          chosenWeakPartial' (d := Module.finrank ℝ E) 2 a
              (chosenWeakPartial' (d := Module.finrank ℝ E) 2 (dirs (Fin.last m))
                (eigenvectorChartIteratedPartial (I := I) (M := M)
                  g r s i α P₀ m (Fin.init dirs)) Ω) Ω =
            chosenWeakPartial' (d := Module.finrank ℝ E) 2 a
              (eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s i α P₀ (m + 1) dirs) Ω := by
        rw [← h_dirs_unfold]
      calc eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s i α P₀ (m + 2) (Fin.cons a dirs)
          = chosenWeakPartial' (d := Module.finrank ℝ E) 2 (dirs (Fin.last m))
              (eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s i α P₀ (m + 1) (Fin.cons a (Fin.init dirs))) Ω :=
            h_lhs_unfold
        _ =ᵐ[(volume : Measure EuclN).restrict Ω]
            chosenWeakPartial' (d := Module.finrank ℝ E) 2 (dirs (Fin.last m))
              (chosenWeakPartial' (d := Module.finrank ℝ E) 2 a
                (eigenvectorChartIteratedPartial (I := I) (M := M)
                  g r s i α P₀ m (Fin.init dirs)) Ω) Ω := h_propagate
        _ =ᵐ[(volume : Measure EuclN).restrict Ω]
            chosenWeakPartial' (d := Module.finrank ℝ E) 2 a
              (chosenWeakPartial' (d := Module.finrank ℝ E) 2 (dirs (Fin.last m))
                (eigenvectorChartIteratedPartial (I := I) (M := M)
                  g r s i α P₀ m (Fin.init dirs)) Ω) Ω := h_swap
        _ = chosenWeakPartial' (d := Module.finrank ℝ E) 2 a
              (eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s i α P₀ (m + 1) dirs) Ω := h_final

omit [CompleteSpace E] in
private theorem eigenvectorIteratedPartial_memWkp_of_chartH_at_all_indices
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    ∀ (m : ℕ) (j : ℕ) (dirs : Fin j → Fin (Module.finrank ℝ E)),
      (∀ idx_all : Fin j → Fin (Module.finrank ℝ E),
        DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) 1 2
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ j idx_all)
          (chartTargetEuclid (I := I) (M := M) α)) →
      (∀ idx_next : Fin (j + 1) → Fin (Module.finrank ℝ E),
        DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) (m + 1) 2
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ (j + 1) idx_next)
          (chartTargetEuclid (I := I) (M := M) α)) →
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) (m + 2) 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ j dirs)
        (chartTargetEuclid (I := I) (M := M) α) := by
  intro m j dirs h_w1p_j h_memWkp_succ
  rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_succ]
  refine ⟨?_, fun a => ?_⟩
  · have h := h_w1p_j dirs
    rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.one_iff_memW1p] at h
    exact h
  · have h_succ_eq :
        eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ (j + 1) (Fin.snoc dirs a) =
          chosenWeakPartial' (d := Module.finrank ℝ E) 2 a
            (eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s i α P₀ j dirs)
            (chartTargetEuclid (I := I) (M := M) α) := by
      rw [eigenvectorChartIteratedPartial_succ]
      have h_last : (Fin.snoc dirs a :
          Fin (j + 1) → Fin (Module.finrank ℝ E)) (Fin.last j) = a :=
        Fin.snoc_last _ _
      have h_init : Fin.init (Fin.snoc dirs a :
          Fin (j + 1) → Fin (Module.finrank ℝ E)) = dirs := Fin.init_snoc _ _
      rw [h_last, h_init]
    have h_next := h_memWkp_succ (Fin.snoc dirs a)
    rw [h_succ_eq] at h_next
    exact h_next

omit [CompleteSpace E] in
theorem eigenvectorChartComponent_memWkp_m_plus_two_of_iterated
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
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have h_general : ∀ (gap : ℕ) (j : ℕ), j + gap = m →
      ∀ (dirs : Fin j → Fin (Module.finrank ℝ E)),
        DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) (gap + 2) 2
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ j dirs)
          (chartTargetEuclid (I := I) (M := M) α) := by
    intro gap
    induction gap with
    | zero =>
        intro j hj dirs
        subst hj
        simpa using h_top_memWkp_two dirs
    | succ gap ih =>
        intro j hj dirs
        have h_engine :=
          eigenvectorIteratedPartial_memWkp_of_chartH_at_all_indices
            (I := I) (M := M) g r s i α P₀ (gap + 1) j dirs
        have hj_le : j ≤ m := by omega
        have h_w1p : ∀ idx_all : Fin j → Fin (Module.finrank ℝ E),
            DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
              (d := Module.finrank ℝ E) 1 2
              (eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s i α P₀ j idx_all)
              (chartTargetEuclid (I := I) (M := M) α) :=
          fun idx_all => h_intermediate_w1p j hj_le idx_all
        have h_succ : ∀ idx_next : Fin (j + 1) → Fin (Module.finrank ℝ E),
            DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
              (d := Module.finrank ℝ E) ((gap + 1) + 1) 2
              (eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s i α P₀ (j + 1) idx_next)
              (chartTargetEuclid (I := I) (M := M) α) := by
          intro idx_next
          have h_ih := ih (j + 1) (by omega) idx_next
          have h_eq : (gap + 1) + 1 = gap + 2 := by ring
          rw [h_eq]
          exact h_ih
        exact h_engine h_w1p h_succ
  have h_final := h_general m 0 (by omega) Fin.elim0
  rw [eigenvectorChartIteratedPartial_zero] at h_final
  exact h_final

section ElaborationTests

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (i : TensorEigenIdx (I := I) (M := M) g r s)

example (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (dirs : Fin m → Fin (Module.finrank ℝ E))
    (a : Fin (Module.finrank ℝ E))
    (h_parent : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (m + 1) 2
      (eigenvectorChartComponentFun (I := I) (M := M) g r s i α P₀)
      (chartTargetEuclid (I := I) (M := M) α)) :
    eigenvectorChartIteratedPartial (I := I) (M := M)
        g r s i α P₀ (m + 1) (Fin.cons a dirs)
      =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)]
    chosenWeakPartial' (d := Module.finrank ℝ E) 2 a
      (eigenvectorChartIteratedPartial (I := I) (M := M)
        g r s i α P₀ m dirs)
      (chartTargetEuclid (I := I) (M := M) α) :=
  eigenvectorChartIteratedPartial_cons_eq_chosenWeakPartial_ae
    g r s i α P₀ m dirs a h_parent

end ElaborationTests

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
