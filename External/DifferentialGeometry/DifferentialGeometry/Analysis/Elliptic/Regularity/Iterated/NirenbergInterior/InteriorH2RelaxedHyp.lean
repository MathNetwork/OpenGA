import DifferentialGeometry.Analysis.Elliptic.Regularity.Iterated.NirenbergInterior.InteriorH2
import DifferentialGeometry.Analysis.Elliptic.Regularity.Iterated.Bootstrap.ChartHm
import DifferentialGeometry.Analysis.Elliptic.Regularity.Iterated.Bootstrap.ChartHmMonotone
import DifferentialGeometry.Analysis.Elliptic.Regularity.Iterated.Bootstrap.ChartHmDomainPow
import DifferentialGeometry.Analysis.Elliptic.Regularity.Iterated.Bootstrap.H2RegularitySuccessor
import DifferentialGeometry.Analysis.Elliptic.Regularity.LaplacianDomain.PowH2kBridge

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace IteratedNirenbergInteriorWeakened

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearUniformDiffQuotBoundCanonical
open DifferentialGeometry.Analysis.Laplacian.ChartH2NonSmooth
open DifferentialGeometry.Analysis.Laplacian.IteratedMixedPartials
open DifferentialGeometry.Analysis.Laplacian.IteratedDifferentiatedData
open DifferentialGeometry.Analysis.Laplacian.TwiceDerivedChartBilinearH1ComplData
open DifferentialGeometry.Analysis.Laplacian.IteratedNirenbergInterior
open DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrap
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private lemma fin_init_cons_aux {α : Type*} {m : ℕ}
    (x : α) (p : Fin (m + 1) → α) :
    Fin.init (Fin.cons x p : Fin (m + 2) → α) =
      Fin.cons x (Fin.init p) := by
  funext j
  induction j using Fin.cases with
  | zero =>
      have h1 : (Fin.init (Fin.cons x p : Fin (m + 2) → α)) 0 = x := by
        simp [Fin.init]
      have h2 : (Fin.cons x (Fin.init p) : Fin (m + 1) → α) 0 = x := by
        simp
      rw [h1, h2]
  | succ k =>
      have h1 : (Fin.init (Fin.cons x p : Fin (m + 2) → α)) (Fin.succ k) =
          p k.castSucc := by
        simp [Fin.init, Fin.cons_succ]
      have h2 : (Fin.cons x (Fin.init p) : Fin (m + 1) → α) (Fin.succ k) =
          p k.castSucc := by
        simp [Fin.init, Fin.cons_succ]
      rw [h1, h2]

private lemma fin_cons_last_succ_aux {α : Type*} {m : ℕ}
    (x : α) (p : Fin (m + 1) → α) :
    (Fin.cons x p : Fin (m + 2) → α) (Fin.last (m + 1)) = p (Fin.last m) := by
  simp

omit [NeZero (Module.finrank ℝ E)] in
theorem chosenMthMixedPartialChartPushedU_cons_eq_chosenWeakPartial_chosenMthMixed_ae_weak
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g) :
    ∀ (m : ℕ) (dirs : Fin m → Fin (Module.finrank ℝ E))
      (i : Fin (Module.finrank ℝ E)),
      MemWkp (d := Module.finrank ℝ E) (m + 1) 2
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
        (chartTargetEuclid (I := I) (M := M) α) →
      chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h (m + 1)
          (Fin.cons i dirs) =ᵐ[
        (volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      chosenWeakPartial' (d := Module.finrank ℝ E) 2 i
        (chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h m dirs)
        (chartTargetEuclid (I := I) (M := M) α) := by
  intro m
  induction m with
  | zero =>
      intro dirs i _h_parent
      have h_lhs_eq :
          chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h 1
              (Fin.cons i dirs) =
            chosenWeakPartial' (d := Module.finrank ℝ E) 2 i
              (chosenMthMixedPartialChartPushedU (I := I) (M := M)
                g α u_h 0 dirs)
              (chartTargetEuclid (I := I) (M := M) α) := by
        rw [chosenMthMixedPartialChartPushedU_succ]
        have h_last : (Fin.cons i dirs : Fin 1 → _) (Fin.last 0) = i := rfl
        have h_init : Fin.init (Fin.cons i dirs : Fin 1 → _) = dirs := by
          funext k
          exact (k.elim0)
        rw [h_last, h_init]
      exact Filter.EventuallyEq.of_eq h_lhs_eq
  | succ m ih =>
      intro dirs i h_parent
      classical
      set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
      have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
      have h_last :
          (Fin.cons i dirs : Fin (m + 2) → Fin (Module.finrank ℝ E))
            (Fin.last (m + 1)) = dirs (Fin.last m) :=
        fin_cons_last_succ_aux i dirs
      have h_init :
          Fin.init (Fin.cons i dirs :
            Fin (m + 2) → Fin (Module.finrank ℝ E)) =
            Fin.cons i (Fin.init dirs) :=
        fin_init_cons_aux i dirs
      have h_lhs_unfold :
          chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h
              (m + 2) (Fin.cons i dirs) =
            chosenWeakPartial' (d := Module.finrank ℝ E) 2
              (dirs (Fin.last m))
              (chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h
                (m + 1) (Fin.cons i (Fin.init dirs))) Ω := by
        rw [chosenMthMixedPartialChartPushedU_succ]
        rw [h_last, h_init]
      have h_dirs_unfold :
          chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h
              (m + 1) dirs =
            chosenWeakPartial' (d := Module.finrank ℝ E) 2
              (dirs (Fin.last m))
              (chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h
                m (Fin.init dirs)) Ω := by
        rw [chosenMthMixedPartialChartPushedU_succ]
      have h_parent_for_ih :
          MemWkp (d := Module.finrank ℝ E) (m + 1) 2
            (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
              ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
            (chartTargetEuclid (I := I) (M := M) α) :=
        MemWkp.le_of_le (by omega) h_parent
      have h_ih := ih (Fin.init dirs) i h_parent_for_ih
      have h_propagate :
          chosenWeakPartial' (d := Module.finrank ℝ E) 2
              (dirs (Fin.last m))
              (chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h
                (m + 1) (Fin.cons i (Fin.init dirs))) Ω =ᵐ[
          (volume : Measure EuclN).restrict Ω]
          chosenWeakPartial' (d := Module.finrank ℝ E) 2
            (dirs (Fin.last m))
            (chosenWeakPartial' (d := Module.finrank ℝ E) 2 i
              (chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h
                m (Fin.init dirs)) Ω) Ω :=
        chosenWeakPartial'_ae_congr (d := Module.finrank ℝ E)
          (p := 2) (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_ih (dirs (Fin.last m))
      have h_inner_memWkp_2_2 :
          MemWkp (d := Module.finrank ℝ E) 2 2
            (chosenMthMixedPartialChartPushedU (I := I) (M := M)
              g α u_h m (Fin.init dirs)) Ω := by
        have h_2_m : (2 : ℕ) + m = m + 2 := by ring
        have h_parent_2_m :
            MemWkp (d := Module.finrank ℝ E) (2 + m) 2
              (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
                ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
              Ω := by
          rw [h_2_m]
          exact h_parent
        exact chosenMthMixedPartialChartPushedU_memWkp_of_chartPushed_memWkp
          (I := I) (M := M) g α u_h m 2 h_parent_2_m (Fin.init dirs)
      have h_swap :=
        chosenWeakPartial'_swap_ae_of_memWkp_two
          hΩ_open h_inner_memWkp_2_2 i (dirs (Fin.last m))
      have h_final :
          chosenWeakPartial' (d := Module.finrank ℝ E) 2 i
              (chosenWeakPartial' (d := Module.finrank ℝ E) 2
                (dirs (Fin.last m))
                (chosenMthMixedPartialChartPushedU (I := I) (M := M)
                  g α u_h m (Fin.init dirs)) Ω) Ω =
            chosenWeakPartial' (d := Module.finrank ℝ E) 2 i
              (chosenMthMixedPartialChartPushedU (I := I) (M := M)
                g α u_h (m + 1) dirs) Ω := by
        rw [← h_dirs_unfold]
      calc chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h
              (m + 2) (Fin.cons i dirs)
          = chosenWeakPartial' (d := Module.finrank ℝ E) 2
              (dirs (Fin.last m))
              (chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h
                (m + 1) (Fin.cons i (Fin.init dirs))) Ω := h_lhs_unfold
        _ =ᵐ[(volume : Measure EuclN).restrict Ω]
            chosenWeakPartial' (d := Module.finrank ℝ E) 2
              (dirs (Fin.last m))
              (chosenWeakPartial' (d := Module.finrank ℝ E) 2 i
                (chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h
                  m (Fin.init dirs)) Ω) Ω := h_propagate
        _ =ᵐ[(volume : Measure EuclN).restrict Ω]
            chosenWeakPartial' (d := Module.finrank ℝ E) 2 i
              (chosenWeakPartial' (d := Module.finrank ℝ E) 2
                (dirs (Fin.last m))
                (chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h
                  m (Fin.init dirs)) Ω) Ω := h_swap
        _ = chosenWeakPartial' (d := Module.finrank ℝ E) 2 i
              (chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h
                (m + 1) dirs) Ω := h_final

omit [NeZero (Module.finrank ℝ E)] in
private lemma iterated_weak_partial_locally_memLp_weak
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g) (m : ℕ)
    (h_parent_m_plus_1 : MemWkp (d := Module.finrank ℝ E) (m + 1) 2
      (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
      (chartTargetEuclid (I := I) (M := M) α))
    (dirs : Fin m → Fin (Module.finrank ℝ E))
    (i : Fin (Module.finrank ℝ E))
    {K : Set EuclN} (hK_compact : IsCompact K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    MemLp
      (chosenWeakPartial' (d := Module.finrank ℝ E) 2 i
        (chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h m dirs)
        (chartTargetEuclid (I := I) (M := M) α)) 2
      ((volume : Measure EuclN).restrict K) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  have h_cons_memLp_global :
      MemLp (chosenMthMixedPartialChartPushedU
        (I := I) (M := M) g α u_h (m + 1) (Fin.cons i dirs)) 2
        ((volume : Measure EuclN).restrict Ω) :=
    chosenMthMixedPartialChartPushedU_memLp_two (I := I) (M := M)
      g α u_h (m + 1) h_parent_m_plus_1 (Fin.cons i dirs)
  have h_schwarz :
      chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h (m + 1)
          (Fin.cons i dirs) =ᵐ[(volume : Measure EuclN).restrict Ω]
      chosenWeakPartial' (d := Module.finrank ℝ E) 2 i
        (chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h m dirs)
        Ω :=
    chosenMthMixedPartialChartPushedU_cons_eq_chosenWeakPartial_chosenMthMixed_ae_weak
      (I := I) (M := M) g α u_h m dirs i h_parent_m_plus_1
  have h_chosen_memLp_global :
      MemLp (chosenWeakPartial' (d := Module.finrank ℝ E) 2 i
        (chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h m dirs) Ω) 2
        ((volume : Measure EuclN).restrict Ω) :=
    (memLp_congr_ae h_schwarz).mp h_cons_memLp_global
  have hK_meas : MeasurableSet K := hK_compact.isClosed.measurableSet
  have h_eq : ((volume : Measure EuclN).restrict Ω).restrict K =
      (volume : Measure EuclN).restrict K := by
    rw [Measure.restrict_restrict hK_meas]
    congr 1
    exact Set.inter_eq_self_of_subset_left hK_in
  rw [← h_eq]
  exact h_chosen_memLp_global.restrict K

private noncomputable def iterated_u_chart_weak
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g) (m : ℕ)
    (dirs : Fin m → Fin (Module.finrank ℝ E)) : EuclN → ℝ :=
  chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h m dirs

private noncomputable def iterated_weak_partial_weak
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g) (m : ℕ)
    (dirs : Fin m → Fin (Module.finrank ℝ E))
    (i : Fin (Module.finrank ℝ E)) : EuclN → ℝ :=
  chosenWeakPartial' (d := Module.finrank ℝ E) 2 i
    (iterated_u_chart_weak (I := I) (M := M) g α u_h m dirs)
    (chartTargetEuclid (I := I) (M := M) α)

noncomputable def iteratedChartBilinearH1ComplData_weak
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g} {m : ℕ}
    (D_m : IteratedDiffChartBilinearData (I := I) (M := M) g α u_h m)
    (h_chart_H_m_plus_1 : MemWkp (d := Module.finrank ℝ E) (m + 1) 2
      (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
      (chartTargetEuclid (I := I) (M := M) α)) :
    ChartBilinearH1ComplData (I := I) (M := M) g α where
  u_chart := iterated_u_chart_weak (I := I) (M := M) g α u_h m D_m.directions
  f_chart := D_m.diffChartForcing
  weak_partial :=
    iterated_weak_partial_weak (I := I) (M := M) g α u_h m D_m.directions
  u_chart_memLp_weighted := by
    have h_parent_m :
        MemWkp (d := Module.finrank ℝ E) m 2
          (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
            ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
          (chartTargetEuclid (I := I) (M := M) α) :=
      MemWkp.le_of_le (by omega) h_chart_H_m_plus_1
    unfold iterated_u_chart_weak
    exact chosenMthMixedPartialChartPushedU_memLp_weighted
      (I := I) (M := M) g α u_h m h_parent_m h_chart_H_m_plus_1 D_m.directions
  f_chart_memLp_weighted := D_m.fChartEff_memLp_weighted
  weak_partial_locally_memLp := fun i _K hK_compact hK_in =>
    iterated_weak_partial_locally_memLp_weak
      (I := I) (M := M) g α u_h m h_chart_H_m_plus_1 D_m.directions i
      hK_compact hK_in
  weak_partial_isWeakPartial := fun i => by
    unfold iterated_weak_partial_weak iterated_u_chart_weak
    have h_memW1p :=
      chosenMthMixedPartialChartPushedU_memW1p_two
        (I := I) (M := M) g α u_h m h_chart_H_m_plus_1 D_m.directions
    exact chosenWeakPartial'_isWeakPartial_of_mem h_memW1p i
  variational_identity := by
    classical
    intro ψ hψ hψ_cs hψ_supp
    have h_in := D_m.m_diff_variational_identity ψ hψ hψ_cs hψ_supp
    set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
    have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
    have h_schwarz_ae : ∀ i : Fin (Module.finrank ℝ E),
        chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h (m + 1)
          (Fin.cons i D_m.directions) =ᵐ[
          (volume : Measure EuclN).restrict Ω]
        chosenWeakPartial' (d := Module.finrank ℝ E) 2 i
          (chosenMthMixedPartialChartPushedU (I := I) (M := M)
            g α u_h m D_m.directions) Ω := fun i =>
      chosenMthMixedPartialChartPushedU_cons_eq_chosenWeakPartial_chosenMthMixed_ae_weak
        (I := I) (M := M) g α u_h m D_m.directions i h_chart_H_m_plus_1
    have h_principal_eq :
        (∫ y in Ω,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i j y *
                chosenMthMixedPartialChartPushedU (I := I) (M := M)
                  g α u_h (m + 1) (Fin.cons i D_m.directions) y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(volume : Measure EuclN)) =
        ∫ y in Ω,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i j y *
                iterated_weak_partial_weak
                  (I := I) (M := M) g α u_h m D_m.directions i y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(volume : Measure EuclN) := by
      refine MeasureTheory.integral_congr_ae ?_
      have h_combined : ∀ᵐ y ∂((volume : Measure EuclN).restrict Ω),
          ∀ i : Fin (Module.finrank ℝ E),
            chosenMthMixedPartialChartPushedU (I := I) (M := M)
              g α u_h (m + 1) (Fin.cons i D_m.directions) y =
            iterated_weak_partial_weak
              (I := I) (M := M) g α u_h m D_m.directions i y := by
        rw [ae_all_iff]
        intro i
        filter_upwards [h_schwarz_ae i] with y hy
        unfold iterated_weak_partial_weak iterated_u_chart_weak
        exact hy
      filter_upwards [h_combined] with y hy
      refine Finset.sum_congr rfl ?_
      intro i _hi
      refine Finset.sum_congr rfl ?_
      intro j _hj
      rw [hy i]
    rw [h_principal_eq] at h_in
    exact h_in


theorem iteratedDerivedChartBilinear_memWkp_two_two_interior_weakened
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g} (m : ℕ)
    (D_m : IteratedDiffChartBilinearData (I := I) (M := M) g α u_h m)
    (h_chart_H_m_plus_1 : MemWkp (d := Module.finrank ℝ E) (m + 1) 2
      (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
      (chartTargetEuclid (I := I) (M := M) α)) :
    ∃ Ω'' : Set EuclN,
      IsOpen Ω'' ∧
      chartImagePOUTsupport (I := I) (M := M) α ⊆ Ω'' ∧
      IsCompact (closure Ω'') ∧
      closure Ω'' ⊆ chartTargetEuclid (I := I) (M := M) α ∧
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) 2 2
        (chosenMthMixedPartialChartPushedU
          (I := I) (M := M) g α u_h m D_m.directions) Ω'' := by
  classical
  set D : ChartBilinearH1ComplData (I := I) (M := M) g α :=
    iteratedChartBilinearH1ComplData_weak (I := I) (M := M) g α D_m
      h_chart_H_m_plus_1
    with hD_def
  set K_α : Set EuclN := chartImagePOUTsupport (I := I) (M := M) α with hK_α_def
  have hK_α_compact : IsCompact K_α :=
    chartImagePOUTsupport_isCompact (I := I) (M := M) α
  have hK_α_in_chart : K_α ⊆ chartTargetEuclid (I := I) (M := M) α :=
    chartImagePOUTsupport_subset_target (I := I) (M := M) α
  have h_chart_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  obtain ⟨R_α, hR_α_pos, hR_α_subset⟩ :=
    hK_α_compact.exists_cthickening_subset_open h_chart_open hK_α_in_chart
  set ε : ℝ := R_α / 16 with hε_def
  have hε_pos : 0 < ε := by positivity
  set R₀ : ℝ := ε with hR₀_def
  have hR₀_pos : 0 < R₀ := hε_pos
  set Ω'' : Set EuclN := Metric.thickening (2 * ε) K_α with hΩ''_def
  have hΩ''_open : IsOpen Ω'' := Metric.isOpen_thickening
  have h_two_ε_pos : 0 < 2 * ε := by positivity
  have hK_α_in_Ω'' : K_α ⊆ Ω'' := Metric.self_subset_thickening h_two_ε_pos K_α
  have h_closureΩ''_sub : closure Ω'' ⊆ Metric.cthickening (2 * ε) K_α := by
    refine closure_minimal (Metric.thickening_subset_cthickening _ _)
      Metric.isClosed_cthickening
  have h_cthick_two_ε_in_chart : Metric.cthickening (2 * ε) K_α ⊆
      chartTargetEuclid (I := I) (M := M) α := by
    have hle : (2 * ε) ≤ R_α := by change 2 * (R_α / 16) ≤ R_α; linarith
    have h := Metric.cthickening_mono hle K_α
    exact h.trans hR_α_subset
  have h_closureΩ''_in_chart :
      closure Ω'' ⊆ chartTargetEuclid (I := I) (M := M) α :=
    h_closureΩ''_sub.trans h_cthick_two_ε_in_chart
  have hΩ''_compact_closure : IsCompact (closure Ω'') :=
    hK_α_compact.cthickening.of_isClosed_subset isClosed_closure h_closureΩ''_sub
  have h_room : Metric.cthickening R₀ (closure Ω'') ⊆
      chartTargetEuclid (I := I) (M := M) α := by
    have h1 : Metric.cthickening R₀ (closure Ω'') ⊆
        Metric.cthickening R₀ (Metric.cthickening (2 * ε) K_α) :=
      Metric.cthickening_subset_of_subset _ h_closureΩ''_sub
    have h2 : Metric.cthickening R₀ (Metric.cthickening (2 * ε) K_α) ⊆
        Metric.cthickening (R₀ + 2 * ε) K_α := by
      apply Metric.cthickening_cthickening_subset
      · positivity
      · positivity
    have h3 : Metric.cthickening (R₀ + 2 * ε) K_α ⊆
        Metric.cthickening R_α K_α := by
      have hle : R₀ + 2 * ε ≤ R_α := by
        change R_α / 16 + 2 * (R_α / 16) ≤ R_α; linarith
      exact Metric.cthickening_mono hle K_α
    exact ((h1.trans h2).trans h3).trans hR_α_subset
  set Ω' : Set EuclN := Metric.thickening (8 * ε) K_α with hΩ'_def
  have hΩ'_open : IsOpen Ω' := Metric.isOpen_thickening
  have h_eight_ε_pos : 0 < 8 * ε := by positivity
  have h_closureΩ'_sub : closure Ω' ⊆ Metric.cthickening (8 * ε) K_α := by
    refine closure_minimal (Metric.thickening_subset_cthickening _ _)
      Metric.isClosed_cthickening
  have h_cthick_eight_ε_in_chart : Metric.cthickening (8 * ε) K_α ⊆
      chartTargetEuclid (I := I) (M := M) α := by
    have hle : (8 * ε) ≤ R_α := by change 8 * (R_α / 16) ≤ R_α; linarith
    have h := Metric.cthickening_mono hle K_α
    exact h.trans hR_α_subset
  have h_closureΩ'_in_chart :
      closure Ω' ⊆ chartTargetEuclid (I := I) (M := M) α :=
    h_closureΩ'_sub.trans h_cthick_eight_ε_in_chart
  have hΩ'_compact_closure : IsCompact (closure Ω') :=
    hK_α_compact.cthickening.of_isClosed_subset isClosed_closure h_closureΩ'_sub
  set K_η : Set EuclN := Metric.cthickening (3 * ε) K_α with hK_η_def
  have hK_η_compact : IsCompact K_η := hK_α_compact.cthickening
  set Ω_η : Set EuclN := Metric.thickening (5 * ε) K_α with hΩ_η_def
  have hΩ_η_open : IsOpen Ω_η := Metric.isOpen_thickening
  have hK_η_in_Ω_η : K_η ⊆ Ω_η := by
    refine Metric.cthickening_subset_thickening' (by positivity) (by linarith) K_α
  obtain ⟨δ_η, η, hδ_η_pos, hδ_η_sub_Ωη, hη_smooth, hη_supp, hη_range,
      hη_one_on_cthick_K_η, hη_tsupp_in_Ω_η⟩ :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_smooth_cutoff_with_neighborhood
      (d := Module.finrank ℝ E) hK_η_compact hΩ_η_open hK_η_in_Ω_η
  obtain ⟨N, hN_pos, h_fderiv_eta⟩ :=
    DifferentialGeometry.Analysis.Sobolev.Chart.exists_grad_bound_of_compactSupport_smooth
      hη_smooth hη_supp
  have hN_nn : 0 ≤ N := hN_pos.le
  have hη_one_on_K_η : ∀ x ∈ K_η, η x = 1 := by
    intro x hx
    apply hη_one_on_cthick_K_η
    exact Metric.self_subset_cthickening _ hx
  have hΩ''_sub_K_η : Ω'' ⊆ K_η := by
    intro y hy
    have h1 : y ∈ Metric.cthickening (2 * ε) K_α :=
      Metric.thickening_subset_cthickening _ _ hy
    refine Metric.cthickening_mono (by linarith : (2 * ε) ≤ 3 * ε) K_α h1
  have hη_one_on_Ω'' : ∀ x ∈ Ω'', η x = 1 :=
    fun x hx => hη_one_on_K_η x (hΩ''_sub_K_η hx)
  have hη_in_Ω' : tsupport η ⊆ Ω' := by
    refine hη_tsupp_in_Ω_η.trans ?_
    rw [hΩ_η_def, hΩ'_def]
    intro y hy
    refine Metric.mem_thickening_iff_infEDist_lt.mpr ?_
    have h := Metric.mem_thickening_iff_infEDist_lt.mp hy
    exact lt_of_lt_of_le h
      (ENNReal.ofReal_le_ofReal (by linarith))
  have hh_supp_in_Ω' : ∀ {h : ℝ}, |h| ≤ R₀ →
      Metric.cthickening |h| (tsupport η) ⊆ Ω' := by
    intro h hh
    have h_tsupp_in_cthick_5ε : tsupport η ⊆ Metric.cthickening (5 * ε) K_α := by
      refine hη_tsupp_in_Ω_η.trans ?_
      rw [hΩ_η_def]
      exact Metric.thickening_subset_cthickening _ _
    by_cases h_abs : |h| ≤ 0
    · have hh_zero : |h| = 0 := le_antisymm h_abs (abs_nonneg _)
      have hcth_zero : Metric.cthickening |h| (tsupport η) = tsupport η := by
        rw [hh_zero, Metric.cthickening_zero]
        exact (isClosed_tsupport η).closure_eq
      rw [hcth_zero]
      exact hη_in_Ω'
    · have h_abs_pos : 0 < |h| := not_le.mp h_abs
      have h1 : Metric.cthickening |h| (tsupport η) ⊆
          Metric.cthickening |h| (Metric.cthickening (5 * ε) K_α) :=
        Metric.cthickening_subset_of_subset _ h_tsupp_in_cthick_5ε
      have h2 : Metric.cthickening |h| (Metric.cthickening (5 * ε) K_α) ⊆
          Metric.cthickening (|h| + 5 * ε) K_α := by
        apply Metric.cthickening_cthickening_subset
        · exact h_abs_pos.le
        · positivity
      have h_le : |h| + 5 * ε < 8 * ε := by
        calc |h| + 5 * ε ≤ R₀ + 5 * ε := by linarith
          _ = ε + 5 * ε := by rw [hR₀_def]
          _ = 6 * ε := by ring
          _ < 8 * ε := by linarith
      have h3 : Metric.cthickening (|h| + 5 * ε) K_α ⊆ Ω' := by
        rw [hΩ'_def]
        exact Metric.cthickening_subset_thickening' (by linarith) h_le K_α
      exact (h1.trans h2).trans h3
  obtain ⟨M_bound, hM_nn, h_uniform_bd⟩ :=
    chartBilinearH1Compl_uniform_diffQuot_bound_of_data
      (I := I) (M := M) (g := g) (α := α) D
      hη_smooth hη_supp hη_range hN_nn h_fderiv_eta
      hΩ'_open h_closureΩ'_in_chart hΩ'_compact_closure
      hη_in_Ω' hR₀_pos hh_supp_in_Ω' hη_one_on_Ω'' hΩ''_open.measurableSet
  have h_h2 :=
    exists_weak_second_partial_of_uniform_diffQuot_bound
      (I := I) (M := M) (g := g) (α := α) D
      hΩ''_open hΩ''_compact_closure hR₀_pos h_room
      hM_nn h_uniform_bd
  have h_uChart_memLp_vol_closureΩ'' :
      MemLp D.u_chart 2 (volume.restrict (closure Ω'')) :=
    memLp_volume_restrict_of_memLp_chartPulledWeightedMeasure (I := I) (M := M)
      D.u_chart_memLp_weighted hΩ''_compact_closure
      hΩ''_compact_closure.isClosed.measurableSet h_closureΩ''_in_chart
  have h_uChart_memLp_vol_Ω'' :
      MemLp D.u_chart 2 (volume.restrict Ω'') :=
    h_uChart_memLp_vol_closureΩ''.mono_measure
      (Measure.restrict_mono subset_closure le_rfl)
  have h_dwp_memLp_Ω'' :
      ∀ i, MemLp (D.weak_partial i) 2 (volume.restrict Ω'') := by
    intro i
    have h := D.weak_partial_locally_memLp i (closure Ω'') hΩ''_compact_closure
      h_closureΩ''_in_chart
    exact h.mono_measure (Measure.restrict_mono subset_closure le_rfl)
  have h_dwp_weak_uChart_Ω'' :
      ∀ i, DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) i
        (D.weak_partial i) D.u_chart Ω'' := by
    intro i
    have h_full : DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) i
        (D.weak_partial i) D.u_chart
        (chartTargetEuclid (I := I) (M := M) α) :=
      D.weak_partial_isWeakPartial i
    have hΩ''_in_chart : Ω'' ⊆ chartTargetEuclid (I := I) (M := M) α :=
      fun y hy => h_closureΩ''_in_chart (subset_closure hy)
    exact DeGiorgi.HasWeakPartialDeriv.restrict hΩ''_open hΩ''_in_chart h_full
  have h_uChart_memW1p_Ω'' :
      DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2 D.u_chart Ω'' := by
    refine ⟨h_uChart_memLp_vol_Ω'', ?_⟩
    intro i
    exact ⟨D.weak_partial i, h_dwp_memLp_Ω'' i, h_dwp_weak_uChart_Ω'' i⟩
  have h_wp_i_memW1p_Ω'' : ∀ i,
      DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2 (D.weak_partial i) Ω'' := by
    intro i
    refine ⟨h_dwp_memLp_Ω'' i, ?_⟩
    intro k
    obtain ⟨g_ik, hg_ik_memLp, hg_ik_partial, _hg_ik_norm⟩ := h_h2 i k
    exact ⟨g_ik, hg_ik_memLp, hg_ik_partial⟩
  have h_uChart_memWkp_two_Ω'' :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) 2 2 D.u_chart Ω'' := by
    refine ⟨h_uChart_memW1p_Ω'', ?_⟩
    intro i
    have h_chosen_partial : DeGiorgi.HasWeakPartialDeriv
        (d := Module.finrank ℝ E) i
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          2 i D.u_chart Ω'') D.u_chart Ω'' :=
      DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_isWeakPartial_of_mem
        h_uChart_memW1p_Ω'' i
    have h_chosen_loc : MeasureTheory.LocallyIntegrable
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          2 i D.u_chart Ω'') (volume.restrict Ω'') :=
      (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_memLp_of_mem
        h_uChart_memW1p_Ω'' i).locallyIntegrable
          (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    have h_dwp_loc : MeasureTheory.LocallyIntegrable (D.weak_partial i)
        (volume.restrict Ω'') :=
      (h_dwp_memLp_Ω'' i).locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    have h_ae :
        DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          2 i D.u_chart Ω'' =ᵐ[volume.restrict Ω''] D.weak_partial i :=
      DeGiorgi.HasWeakPartialDeriv.ae_eq hΩ''_open h_chosen_partial
        (h_dwp_weak_uChart_Ω'' i) h_chosen_loc h_dwp_loc
    rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.one_iff_memW1p]
    exact (DifferentialGeometry.Analysis.Sobolev.Euclidean.MemW1p_congr_ae
      hΩ''_open h_ae.symm).mp (h_wp_i_memW1p_Ω'' i)
  refine ⟨Ω'', hΩ''_open, hK_α_in_Ω'', hΩ''_compact_closure,
    h_closureΩ''_in_chart, ?_⟩
  exact h_uChart_memWkp_two_Ω''

end IteratedNirenbergInteriorWeakened
end Laplacian
end Analysis
end DifferentialGeometry

end
