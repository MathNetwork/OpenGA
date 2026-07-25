import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Iterated.EigenvectorIteratedData
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Iterated.EigenvectorIteratedRegularityHigher

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
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open DifferentialGeometry.Analysis.Sobolev.Chart
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open DifferentialGeometry.Analysis.Sobolev.Euclidean

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

private def eigenvectorIteratedChartBilinearH1ComplData
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) {m : ℕ}
    (D_m : eigenvectorIteratedTensorChartBilinearData (I := I) (M := M)
      g r s i α P₀ m)
    (h_parent : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (m + 1) 2
      (eigenvectorChartComponentFun (I := I) (M := M) g r s i α P₀)
      (chartTargetEuclid (I := I) (M := M) α)) :
    ChartBilinearH1ComplData (I := I) (M := M) g α where
  u_chart :=
    eigenvectorChartIteratedPartial (I := I) (M := M)
      g r s i α P₀ m D_m.directions
  f_chart := D_m.diffChartForcing
  weak_partial := fun j =>
    chosenWeakPartial' (d := Module.finrank ℝ E) 2 j
      (eigenvectorChartIteratedPartial (I := I) (M := M)
        g r s i α P₀ m D_m.directions)
      (chartTargetEuclid (I := I) (M := M) α)
  u_chart_memLp_weighted := by
      set K : Set EuclN := chartPouKernel (I := I) (M := M) α with hK_def
      have hK_compact : IsCompact K :=
        chartPouKernel_isCompact (I := I) (M := M) α
      have hK_meas : MeasurableSet K :=
        chartPouKernel_measurableSet (I := I) (M := M) α
      have hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α :=
        chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α
      have h_plain : MemLp (eigenvectorChartIteratedPartial
          (I := I) (M := M)
          g r s i α P₀ m D_m.directions) 2
          ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)) :=
        eigenvectorChartIteratedPartial_memLp_volume
          (I := I) (M := M) g r s i α P₀ m D_m.directions
      have h_off : ∀ᵐ y ∂((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)),
          y ∉ K → eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ m D_m.directions y = 0 := by
        have h_ae := eigenvectorChartIteratedPartial_ae_zero_off_chartPouKernel
          (I := I) (M := M) g r s i α P₀ m D_m.directions
        have hΩ_meas : MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
          (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet
        have hV_meas : MeasurableSet (chartTargetEuclid (I := I) (M := M) α \ K) :=
          (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet.diff hK_meas
        rw [ae_restrict_iff' hΩ_meas]
        rw [Filter.EventuallyEq, ae_restrict_iff' hV_meas] at h_ae
        filter_upwards [h_ae] with y hy
        intro hy_chart hy_off
        exact hy ⟨hy_chart, hy_off⟩
      exact memLp_chartPulledWeightedMeasure_of_memLp_volume_of_ae_zero_off_compact
        (I := I) (M := M) g α hK_compact hK_meas hK_in h_off h_plain
  f_chart_memLp_weighted := D_m.fChartEff_memLp_weighted
  weak_partial_locally_memLp := by
      intro j K hK_compact hK_in
      have h_parent' :
          DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
            (d := Module.finrank ℝ E) (1 + m) 2
            (eigenvectorChartComponentFun (I := I) (M := M)
              g r s i α P₀)
            (chartTargetEuclid (I := I) (M := M) α) := by
        rw [Nat.add_comm 1 m]
        exact h_parent
      have h_memWkp_one :=
        eigenvectorChartIteratedPartial_memWkp_of_memWkp
          (I := I) (M := M) g r s i α P₀ m 1 h_parent' D_m.directions
      rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.one_iff_memW1p]
        at h_memWkp_one
      have h_chosen_memLp :=
        chosenWeakPartial'_memLp_of_mem h_memWkp_one j
      have hK_meas : MeasurableSet K := hK_compact.isClosed.measurableSet
      have h_eq : ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)).restrict K =
          (volume : Measure EuclN).restrict K := by
        rw [Measure.restrict_restrict hK_meas]
        congr 1
        exact Set.inter_eq_self_of_subset_left hK_in
      rw [← h_eq]
      exact h_chosen_memLp.restrict K
  weak_partial_isWeakPartial := by
      intro j
      have h_parent' :
          DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
            (d := Module.finrank ℝ E) (1 + m) 2
            (eigenvectorChartComponentFun (I := I) (M := M)
              g r s i α P₀)
            (chartTargetEuclid (I := I) (M := M) α) := by
        rw [Nat.add_comm 1 m]
        exact h_parent
      have h_memWkp_one :=
        eigenvectorChartIteratedPartial_memWkp_of_memWkp
          (I := I) (M := M) g r s i α P₀ m 1 h_parent' D_m.directions
      rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.one_iff_memW1p]
        at h_memWkp_one
      exact chosenWeakPartial'_isWeakPartial_of_mem h_memWkp_one j
  variational_identity := by
      classical
      intro ψ hψ hψ_cs hψ_supp
      have h_in := D_m.m_diff_variational_identity ψ hψ hψ_cs hψ_supp
      set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
      have h_schwarz : ∀ a : Fin (Module.finrank ℝ E),
          eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s i α P₀ (m + 1) (Fin.cons a D_m.directions)
            =ᵐ[(volume : Measure EuclN).restrict Ω]
          chosenWeakPartial' (d := Module.finrank ℝ E) 2 a
            (eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s i α P₀ m D_m.directions) Ω := fun a =>
        eigenvectorChartIteratedPartial_cons_eq_chosenWeakPartial_ae
          (I := I) (M := M) g r s i α P₀ m D_m.directions a h_parent
      have h_principal_eq :
          (∫ y in Ω,
            (∑ a : Fin (Module.finrank ℝ E),
              ∑ b : Fin (Module.finrank ℝ E),
                weightedInvGramOnEuclid (I := I) g α a b y *
                  eigenvectorChartIteratedPartial (I := I) (M := M)
                    g r s i α P₀ (m + 1)
                    (Fin.cons a D_m.directions) y *
                  (fderiv ℝ ψ y) (EuclideanSpace.single b 1))
            ∂(volume : Measure EuclN)) =
          ∫ y in Ω,
            (∑ a : Fin (Module.finrank ℝ E),
              ∑ b : Fin (Module.finrank ℝ E),
                weightedInvGramOnEuclid (I := I) g α a b y *
                  chosenWeakPartial' (d := Module.finrank ℝ E) 2 a
                    (eigenvectorChartIteratedPartial (I := I) (M := M)
                      g r s i α P₀ m D_m.directions) Ω y *
                  (fderiv ℝ ψ y) (EuclideanSpace.single b 1))
            ∂(volume : Measure EuclN) := by
        refine MeasureTheory.integral_congr_ae ?_
        have h_combined : ∀ᵐ y ∂((volume : Measure EuclN).restrict Ω),
            ∀ a : Fin (Module.finrank ℝ E),
              eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s i α P₀ (m + 1)
                (Fin.cons a D_m.directions) y =
              chosenWeakPartial' (d := Module.finrank ℝ E) 2 a
                (eigenvectorChartIteratedPartial (I := I) (M := M)
                  g r s i α P₀ m D_m.directions) Ω y := by
          rw [ae_all_iff]
          intro a
          filter_upwards [h_schwarz a] with y hy
          exact hy
        filter_upwards [h_combined] with y hy
        refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
        rw [hy a]
      rw [h_principal_eq] at h_in
      exact h_in

def eigenvectorIteratedTensorChartBilinearData_toData
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) {m : ℕ}
    (D_m : eigenvectorIteratedTensorChartBilinearData (I := I) (M := M)
      g r s i α P₀ m)
    (h_parent : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (m + 1) 2
      (eigenvectorChartComponentFun (I := I) (M := M) g r s i α P₀)
      (chartTargetEuclid (I := I) (M := M) α)) :
    TensorChartBilinearH1ComplData (I := I) (M := M) g r s α P₀ where
  toChartData :=
    eigenvectorIteratedChartBilinearH1ComplData
      (I := I) (M := M) g r s i α P₀ D_m h_parent

omit [CompleteSpace E] in
theorem eigenvectorChartIteratedPartial_memWkp_two_two
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) {m : ℕ}
    (directions : Fin m → Fin (Module.finrank ℝ E))
    (D_m : eigenvectorIteratedTensorChartBilinearData (I := I) (M := M)
      g r s i α P₀ m)
    (h_dir : D_m.directions = directions)
    (h_parent : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (m + 1) 2
      (eigenvectorChartComponentFun (I := I) (M := M) g r s i α P₀)
      (chartTargetEuclid (I := I) (M := M) α)) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 2 2
      (eigenvectorChartIteratedPartial (I := I) (M := M)
        g r s i α P₀ m directions)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set D : TensorChartBilinearH1ComplData (I := I) (M := M) g r s α P₀ :=
    eigenvectorIteratedTensorChartBilinearData_toData
      (I := I) (M := M) g r s i α P₀ D_m h_parent
    with hD_def
  have hD_u_chart : D.u_chart =
      eigenvectorChartIteratedPartial (I := I) (M := M)
        g r s i α P₀ m D_m.directions := rfl
  set K : Set EuclN := chartPouKernel (I := I) (M := M) α with hK_def
  have hK_compact : IsCompact K := chartPouKernel_isCompact (I := I) (M := M) α
  have hK_meas : MeasurableSet K :=
    chartPouKernel_measurableSet (I := I) (M := M) α
  have hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α :=
    chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α
  have h_chart_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  obtain ⟨R_α, hR_α_pos, hR_α_subset⟩ :=
    hK_compact.exists_cthickening_subset_open h_chart_open hK_in
  set Ω'' : Set EuclN := Metric.thickening (R_α / 2) K with hΩ''_def
  have hΩ''_open : IsOpen Ω'' := Metric.isOpen_thickening
  have h_half_pos : 0 < R_α / 2 := by positivity
  have hK_in_Ω'' : K ⊆ Ω'' := Metric.self_subset_thickening h_half_pos K
  have h_closureΩ''_sub : closure Ω'' ⊆ Metric.cthickening (R_α / 2) K :=
    closure_minimal (Metric.thickening_subset_cthickening _ _)
      Metric.isClosed_cthickening
  have h_cthick_half_in_chart : Metric.cthickening (R_α / 2) K ⊆
      chartTargetEuclid (I := I) (M := M) α := by
    have hle : (R_α / 2) ≤ R_α := by linarith
    exact (Metric.cthickening_mono hle K).trans hR_α_subset
  have h_closureΩ''_in_chart :
      closure Ω'' ⊆ chartTargetEuclid (I := I) (M := M) α :=
    h_closureΩ''_sub.trans h_cthick_half_in_chart
  have hΩ''_compact_closure : IsCompact (closure Ω'') :=
    hK_compact.cthickening.of_isClosed_subset isClosed_closure h_closureΩ''_sub
  set R₀ : ℝ := R_α / 4 with hR₀_def
  have hR₀_pos : 0 < R₀ := by positivity
  have h_room : Metric.cthickening R₀ (closure Ω'') ⊆
      chartTargetEuclid (I := I) (M := M) α := by
    have h1 : Metric.cthickening R₀ (closure Ω'') ⊆
        Metric.cthickening R₀ (Metric.cthickening (R_α / 2) K) :=
      Metric.cthickening_subset_of_subset _ h_closureΩ''_sub
    have h2 : Metric.cthickening R₀ (Metric.cthickening (R_α / 2) K) ⊆
        Metric.cthickening (R₀ + R_α / 2) K := by
      apply Metric.cthickening_cthickening_subset
      · positivity
      · positivity
    have h3 : Metric.cthickening (R₀ + R_α / 2) K ⊆
        Metric.cthickening R_α K := by
      have hle : R₀ + R_α / 2 ≤ R_α := by rw [hR₀_def]; linarith
      exact Metric.cthickening_mono hle K
    exact ((h1.trans h2).trans h3).trans hR_α_subset
  obtain ⟨h_uChart_memW1p, h_wp_memW1p⟩ :=
    tensorChartBilinear_chartComponent_regularity_of_data
      (g := g) (r := r) (s := s) (α := α) (P₀ := P₀) D
      hΩ''_open hΩ''_compact_closure hR₀_pos h_room
  have h_uChart_memWkp_two_Ω'' :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) 2 2 D.u_chart Ω'' := by
    refine ⟨h_uChart_memW1p, fun j => ?_⟩
    have hΩ''_in_chart : Ω'' ⊆ chartTargetEuclid (I := I) (M := M) α :=
      fun y hy => h_closureΩ''_in_chart (subset_closure hy)
    have h_dwp_weak_uChart_Ω'' : DeGiorgi.HasWeakPartialDeriv
        (d := Module.finrank ℝ E) j (D.weak_partial j) D.u_chart Ω'' :=
      DeGiorgi.HasWeakPartialDeriv.restrict hΩ''_open hΩ''_in_chart
        (D.weak_partial_isWeakPartial j)
    have h_chosen_partial : DeGiorgi.HasWeakPartialDeriv
        (d := Module.finrank ℝ E) j
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          2 j D.u_chart Ω'') D.u_chart Ω'' :=
      DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_isWeakPartial_of_mem
        h_uChart_memW1p j
    have h_chosen_loc : MeasureTheory.LocallyIntegrable
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          2 j D.u_chart Ω'') ((volume : Measure EuclN).restrict Ω'') :=
      (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_memLp_of_mem
        h_uChart_memW1p j).locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    have h_dwp_loc : MeasureTheory.LocallyIntegrable (D.weak_partial j)
        ((volume : Measure EuclN).restrict Ω'') :=
      (h_wp_memW1p j).1.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    have h_ae :
        DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          2 j D.u_chart Ω'' =ᵐ[(volume : Measure EuclN).restrict Ω'']
            D.weak_partial j :=
      DeGiorgi.HasWeakPartialDeriv.ae_eq hΩ''_open h_chosen_partial
        h_dwp_weak_uChart_Ω'' h_chosen_loc h_dwp_loc
    rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.one_iff_memW1p]
    exact (DifferentialGeometry.Analysis.Sobolev.Euclidean.MemW1p_congr_ae
      hΩ''_open h_ae.symm).mp (h_wp_memW1p j)
  rw [hD_u_chart] at h_uChart_memWkp_two_Ω''
  have h_global_Lp : MemLp (eigenvectorChartIteratedPartial
      (I := I) (M := M)
      g r s i α P₀ m D_m.directions) 2
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) :=
    eigenvectorChartIteratedPartial_memLp_volume
      (I := I) (M := M) g r s i α P₀ m D_m.directions
  have h_ae_zero : eigenvectorChartIteratedPartial (I := I) (M := M)
      g r s i α P₀ m D_m.directions
      =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \ K)] 0 :=
    eigenvectorChartIteratedPartial_ae_zero_off_chartPouKernel
      (I := I) (M := M) g r s i α P₀ m D_m.directions
  have h_global :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) 2 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ m D_m.directions)
        (chartTargetEuclid (I := I) (M := M) α) :=
    MemWkp_of_memWkp_precompact_of_ae_zero_off_compact
      (d := Module.finrank ℝ E) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
      h_chart_open hΩ''_open hK_compact hK_in_Ω'' h_closureΩ''_in_chart
      h_global_Lp h_ae_zero h_uChart_memWkp_two_Ω''
  rw [h_dir] at h_global
  exact h_global

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
