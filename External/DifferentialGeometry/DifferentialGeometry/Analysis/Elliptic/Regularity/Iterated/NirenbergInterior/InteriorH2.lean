import DifferentialGeometry.Analysis.Elliptic.Regularity.Iterated.VariationalIdentity.DifferentiatedData
import DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.TwiceDifferentiated.DerivedData
import DifferentialGeometry.Analysis.Elliptic.Regularity.ChartBilinear.UniformDiffQuotBoundFromDomain
import DifferentialGeometry.Analysis.Elliptic.Regularity.ChartHk.H2NonSmooth
import DifferentialGeometry.Analysis.Sobolev.Approximation.SmoothDensity


noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace IteratedNirenbergInterior

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
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private lemma fin_init_cons {α : Type*} {m : ℕ}
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

private lemma fin_cons_last_succ {α : Type*} {m : ℕ}
    (x : α) (p : Fin (m + 1) → α) :
    (Fin.cons x p : Fin (m + 2) → α) (Fin.last (m + 1)) = p (Fin.last m) := by
  simp

omit [NeZero (Module.finrank ℝ E)] in
theorem chosenMthMixedPartialChartPushedU_cons_eq_chosenWeakPartial_chosenMthMixed_ae
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g) :
    ∀ (m : ℕ) (dirs : Fin m → Fin (Module.finrank ℝ E))
      (i : Fin (Module.finrank ℝ E)),
      MemWkp (d := Module.finrank ℝ E) (m + 2) 2
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
        fin_cons_last_succ i dirs
      have h_init :
          Fin.init (Fin.cons i dirs :
            Fin (m + 2) → Fin (Module.finrank ℝ E)) =
            Fin.cons i (Fin.init dirs) :=
        fin_init_cons i dirs
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
          MemWkp (d := Module.finrank ℝ E) (m + 2) 2
            (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
              ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
            (chartTargetEuclid (I := I) (M := M) α) := by
        exact MemWkp.le_of_le (by omega) h_parent
      have h_ih :=
        ih (Fin.init dirs) i h_parent_for_ih
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
          exact h_parent_for_ih
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
private lemma chartTarget_diff_chartImagePOUTsupport_isOpen_aux (α : M) :
    IsOpen ((chartTargetEuclid (I := I) (M := M) α) \
      chartImagePOUTsupport (I := I) (M := M) α) :=
  (chartTargetEuclid_isOpen (I := I) (M := M) α).sdiff
    (chartImagePOUTsupport_isCompact (I := I) (M := M) α).isClosed

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma chartTarget_diff_chartImagePOUTsupport_subset_aux (α : M) :
    (chartTargetEuclid (I := I) (M := M) α) \
        chartImagePOUTsupport (I := I) (M := M) α ⊆
      chartTargetEuclid (I := I) (M := M) α :=
  Set.diff_subset

omit [NeZero (Module.finrank ℝ E)] in
private lemma chartPushed_ae_zero_off_chartImagePOUTsupport_aux
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g) :
    ∀ᵐ y ∂((volume : Measure EuclN).restrict
      ((chartTargetEuclid (I := I) (M := M) α) \
        chartImagePOUTsupport (I := I) (M := M) α)),
      chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ) y = 0 := by
  classical
  have h_diff_meas : MeasurableSet
      ((chartTargetEuclid (I := I) (M := M) α) \
        chartImagePOUTsupport (I := I) (M := M) α) :=
    (chartTarget_diff_chartImagePOUTsupport_isOpen_aux (I := I) (M := M) α).measurableSet
  refine (ae_restrict_iff' h_diff_meas).mpr ?_
  refine Filter.Eventually.of_forall ?_
  intro y hy
  exact chartPushed_eq_zero_off_chartImagePOUTsupport (I := I) (M := M) α _
    hy.1 hy.2

omit [NeZero (Module.finrank ℝ E)] in
private lemma locallyIntegrableOn_of_memLp_two_chartTarget_aux
    (α : M) {f : EuclN → ℝ}
    (hf : MemLp f 2
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α))) :
    LocallyIntegrableOn f
      ((chartTargetEuclid (I := I) (M := M) α) \
        chartImagePOUTsupport (I := I) (M := M) α)
      (volume : Measure EuclN) := by
  classical
  have hU_open := chartTarget_diff_chartImagePOUTsupport_isOpen_aux (I := I) (M := M) α
  intro x hx
  obtain ⟨r, hr_pos, hr_subset⟩ := Metric.isOpen_iff.mp hU_open x hx
  set B : Set EuclN := Metric.closedBall x (r / 2) with hB_def
  have hB_compact : IsCompact B := isCompact_closedBall _ _
  have hB_subset_U : B ⊆ (chartTargetEuclid (I := I) (M := M) α) \
      chartImagePOUTsupport (I := I) (M := M) α := by
    intro y hy
    apply hr_subset
    rw [Metric.mem_ball]
    rw [Metric.mem_closedBall] at hy
    linarith [hy, hr_pos]
  have hB_subset_Ω : B ⊆ chartTargetEuclid (I := I) (M := M) α :=
    hB_subset_U.trans
      (chartTarget_diff_chartImagePOUTsupport_subset_aux (I := I) (M := M) α)
  have hB_meas : MeasurableSet B := hB_compact.isClosed.measurableSet
  have h_restrict : MemLp f 2
      (((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)).restrict B) := hf.restrict B
  have h_eq : ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)).restrict B =
        (volume : Measure EuclN).restrict B := by
    rw [Measure.restrict_restrict hB_meas]
    congr 1
    exact Set.inter_eq_self_of_subset_left hB_subset_Ω
  rw [h_eq] at h_restrict
  have hB_finite : (volume : Measure EuclN) B < ⊤ := hB_compact.measure_lt_top
  haveI hB_isFin : IsFiniteMeasure ((volume : Measure EuclN).restrict B) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    exact hB_finite
  have h_int : IntegrableOn f B (volume : Measure EuclN) :=
    h_restrict.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  refine ⟨B, ?_, h_int⟩
  refine Filter.mem_inf_of_left ?_
  apply Filter.mem_of_superset (Metric.ball_mem_nhds x (by linarith : 0 < r / 2))
  exact Metric.ball_subset_closedBall

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma weakPartial_ae_zero_off_inline_aux
    {Ω U : Set EuclN} (hΩ_open : IsOpen Ω) (hU_open : IsOpen U)
    (hU_sub : U ⊆ Ω)
    {f w : EuclN → ℝ}
    (i : Fin (Module.finrank ℝ E))
    (hw_isWeak : DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) i w f Ω)
    (hw_li : LocallyIntegrableOn w U (volume : Measure EuclN))
    (hf_ae_zero : ∀ᵐ y ∂((volume : Measure EuclN).restrict U), f y = 0) :
    ∀ᵐ y ∂((volume : Measure EuclN).restrict U), w y = 0 := by
  classical
  have hU_meas : MeasurableSet U := hU_open.measurableSet
  have hf_ae_zero_vol : ∀ᵐ y ∂(volume : Measure EuclN), y ∈ U → f y = 0 := by
    rw [← ae_restrict_iff' hU_meas]; exact hf_ae_zero
  have h_target : ∀ᵐ y ∂(volume : Measure EuclN), y ∈ U → w y = 0 := by
    apply hU_open.ae_eq_zero_of_integral_contDiff_smul_eq_zero hw_li
    intro ψ hψ_smooth hψ_cs hψ_supp
    have hψ_supp_Ω : tsupport ψ ⊆ Ω := hψ_supp.trans hU_sub
    have hΩ_meas : MeasurableSet Ω := hΩ_open.measurableSet
    have h_weak := hw_isWeak ψ hψ_smooth hψ_cs hψ_supp_Ω
    have h_f_supp_ae : ∀ᵐ y ∂((volume : Measure EuclN).restrict Ω),
        f y * (fderiv ℝ ψ y) (EuclideanSpace.single i 1) = 0 := by
      refine (ae_restrict_iff' hΩ_meas).mpr ?_
      filter_upwards [hf_ae_zero_vol] with y hy _hyΩ
      by_cases hy_U : y ∈ U
      · rw [hy hy_U]; ring
      · have h_compl_open : IsOpen ((tsupport ψ)ᶜ) :=
          (isClosed_tsupport _).isOpen_compl
        have h_y_not_supp : y ∉ tsupport ψ := fun h => hy_U (hψ_supp h)
        have h_zero_nbhd : ∀ᶠ z in 𝓝 y, ψ z = 0 := by
          filter_upwards [h_compl_open.mem_nhds h_y_not_supp] with z hz
          exact image_eq_zero_of_notMem_tsupport hz
        have h_fderiv_zero : fderiv ℝ ψ y = 0 := by
          have h_ev_const : ψ =ᶠ[𝓝 y] (fun _ : EuclN => (0 : ℝ)) := h_zero_nbhd
          rw [Filter.EventuallyEq.fderiv_eq h_ev_const]; simp
        rw [h_fderiv_zero]; simp
    have h_zero_lhs :
        ∫ y in Ω, f y * (fderiv ℝ ψ y) (EuclideanSpace.single i 1)
          ∂(volume : Measure EuclN) = 0 := by
      rw [MeasureTheory.integral_congr_ae h_f_supp_ae]; simp
    rw [h_zero_lhs] at h_weak
    have h_rhs_zero :
        ∫ y in Ω, w y * ψ y ∂(volume : Measure EuclN) = 0 := by linarith
    have h_vanish_off_Ω : ∀ x ∉ Ω, ψ x • w x = 0 := fun x hx => by
      have hx_supp : x ∉ tsupport ψ := fun h => hx (hψ_supp_Ω h)
      have hψ_x : ψ x = 0 := image_eq_zero_of_notMem_tsupport hx_supp
      rw [hψ_x]; simp
    rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      h_vanish_off_Ω]
    refine (MeasureTheory.setIntegral_congr_fun hΩ_meas ?_).trans h_rhs_zero
    intro x _hxΩ; simp [smul_eq_mul, mul_comm]
  refine (ae_restrict_iff' hU_meas).mpr ?_
  filter_upwards [h_target] with y hy hy_U
  exact hy hy_U

omit [NeZero (Module.finrank ℝ E)] in
lemma chosenMthMixedPartialChartPushedU_ae_zero_off_chartImagePOUTsupport
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g) :
    ∀ (m : ℕ),
      MemWkp (d := Module.finrank ℝ E) (m + 1) 2
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
        (chartTargetEuclid (I := I) (M := M) α) →
      ∀ (dirs : Fin m → Fin (Module.finrank ℝ E)),
        ∀ᵐ y ∂((volume : Measure EuclN).restrict
          ((chartTargetEuclid (I := I) (M := M) α) \
            chartImagePOUTsupport (I := I) (M := M) α)),
          chosenMthMixedPartialChartPushedU (I := I) (M := M)
            g α u_h m dirs y = 0 := by
  intro m
  induction m with
  | zero =>
      intro _h_parent dirs
      simp only [chosenMthMixedPartialChartPushedU_zero]
      exact chartPushed_ae_zero_off_chartImagePOUTsupport_aux
        (I := I) (M := M) g α u_h
  | succ m ih =>
      intro h_parent dirs
      classical
      set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
      have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
      set U : Set EuclN := Ω \ chartImagePOUTsupport (I := I) (M := M) α
      have hU_open : IsOpen U :=
        chartTarget_diff_chartImagePOUTsupport_isOpen_aux (I := I) (M := M) α
      have hU_sub : U ⊆ Ω :=
        chartTarget_diff_chartImagePOUTsupport_subset_aux (I := I) (M := M) α
      have h_parent_for_ih :
          MemWkp (d := Module.finrank ℝ E) (m + 1) 2
            (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
              ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
            (chartTargetEuclid (I := I) (M := M) α) :=
        MemWkp.le_of_le (by omega) h_parent
      have h_ih_zero := ih h_parent_for_ih (Fin.init dirs)
      have h_inner_memW1p :
          DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
            (chosenMthMixedPartialChartPushedU (I := I) (M := M)
              g α u_h m (Fin.init dirs)) Ω := by
        have h_parent_1_m :
            MemWkp (d := Module.finrank ℝ E) (1 + m) 2
              (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
                ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
              Ω := by
          have h_1m : 1 + m = m + 1 := Nat.add_comm 1 m
          rw [h_1m]
          exact h_parent_for_ih
        have h_step :=
          chosenMthMixedPartialChartPushedU_memWkp_of_chartPushed_memWkp
            (I := I) (M := M) g α u_h m 1 h_parent_1_m (Fin.init dirs)
        rw [MemWkp.one_iff_memW1p] at h_step
        exact h_step
      have h_isWeak :=
        chosenWeakPartial'_isWeakPartial_of_mem h_inner_memW1p
          (dirs (Fin.last m))
      have h_chosen_memLp :=
        chosenWeakPartial'_memLp_of_mem h_inner_memW1p (dirs (Fin.last m))
      have hw_li := locallyIntegrableOn_of_memLp_two_chartTarget_aux
        (I := I) (M := M) (α := α) (f := _) h_chosen_memLp
      rw [chosenMthMixedPartialChartPushedU_succ]
      exact weakPartial_ae_zero_off_inline_aux hΩ_open hU_open hU_sub
        (i := dirs (Fin.last m)) h_isWeak hw_li h_ih_zero

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma chartPulledWeighted_le_volume_on_compact_aux
    {g : SmoothRiemannianMetric I M} (α : M)
    {K : Set EuclN} (hK_compact : IsCompact K)
    (hK_meas : MeasurableSet K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ∃ c : ℝ, 0 < c ∧
      (chartPulledWeightedMeasure (I := I) g α).restrict K ≤
        ENNReal.ofReal c • ((volume : Measure EuclN).restrict K) := by
  classical
  obtain ⟨_c_min, c_max, hc_min_pos, hc_le, h_bd⟩ :=
    densityOnEuclid_bounded_on_compact (I := I) (M := M) g α hK_compact hK_in
  refine ⟨c_max, lt_of_lt_of_le hc_min_pos hc_le, ?_⟩
  refine Measure.le_iff.2 ?_
  intro A hA
  rw [Measure.restrict_apply hA, Measure.smul_apply,
    Measure.restrict_apply hA]
  unfold chartPulledWeightedMeasure
  rw [withDensity_apply _ (hA.inter hK_meas)]
  have h_pointwise_bd :
      ∫⁻ y in A ∩ K,
          ENNReal.ofReal (densityOnEuclid (I := I) g α y)
            ∂(volume : Measure EuclN) ≤
      ∫⁻ _y in A ∩ K, ENNReal.ofReal c_max ∂(volume : Measure EuclN) := by
    apply MeasureTheory.setLIntegral_mono_ae'
    · exact hA.inter hK_meas
    · refine Filter.Eventually.of_forall fun y hy => ?_
      apply ENNReal.ofReal_le_ofReal
      exact (h_bd y hy.2).2
  have h_const_eval :
      ∫⁻ _y in A ∩ K, ENNReal.ofReal c_max ∂(volume : Measure EuclN) =
      ENNReal.ofReal c_max * (volume : Measure EuclN) (A ∩ K) := by
    rw [MeasureTheory.setLIntegral_const]
  rw [smul_eq_mul]
  exact h_pointwise_bd.trans (le_of_eq h_const_eval)

omit [NeZero (Module.finrank ℝ E)] in
lemma chosenMthMixedPartialChartPushedU_memLp_weighted
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g)
    (m : ℕ)
    (h_parent_m : MemWkp (d := Module.finrank ℝ E) m 2
      (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
      (chartTargetEuclid (I := I) (M := M) α))
    (h_parent_m_plus_1 : MemWkp (d := Module.finrank ℝ E) (m + 1) 2
      (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
      (chartTargetEuclid (I := I) (M := M) α))
    (dirs : Fin m → Fin (Module.finrank ℝ E)) :
    MemLp (chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h m dirs)
      2 ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  have h_global : MemLp
      (chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h m dirs) 2
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) :=
    chosenMthMixedPartialChartPushedU_memLp_two (I := I) (M := M)
      g α u_h m h_parent_m dirs
  have h_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  set K : Set EuclN := chartImagePOUTsupport (I := I) (M := M) α with hK_def
  have hK_compact : IsCompact K :=
    chartImagePOUTsupport_isCompact (I := I) (M := M) α
  have hK_meas : MeasurableSet K := hK_compact.isClosed.measurableSet
  have hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α :=
    chartImagePOUTsupport_subset_target (I := I) (M := M) α
  have h_ae_zero_off_K_raw :=
    chosenMthMixedPartialChartPushedU_ae_zero_off_chartImagePOUTsupport
      (I := I) (M := M) g α u_h m h_parent_m_plus_1 dirs
  have h_ae_zero_off_K :
      ∀ᵐ y ∂((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)),
        y ∉ K → chosenMthMixedPartialChartPushedU
          (I := I) (M := M) g α u_h m dirs y = 0 := by
    have hΩ_meas : MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
      h_open.measurableSet
    have hU_meas : MeasurableSet
        ((chartTargetEuclid (I := I) (M := M) α) \ K) :=
      (chartTarget_diff_chartImagePOUTsupport_isOpen_aux (I := I) (M := M) α).measurableSet
    rw [ae_restrict_iff' hΩ_meas]
    have h_raw_vol := (ae_restrict_iff' hU_meas).mp h_ae_zero_off_K_raw
    filter_upwards [h_raw_vol] with y hy hyΩ hy_notK
    have hy_in_diff : y ∈ (chartTargetEuclid (I := I) (M := M) α) \ K :=
      ⟨hyΩ, hy_notK⟩
    exact hy hy_in_diff
  set u_chart : EuclN → ℝ :=
    chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h m dirs
  have h_u_eq_ind :
      u_chart =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)] K.indicator u_chart := by
    filter_upwards [h_ae_zero_off_K] with y hy
    by_cases hy_K : y ∈ K
    · simp [Set.indicator_of_mem hy_K]
    · rw [Set.indicator_of_notMem hy_K, hy hy_K]
  have h_global_K : MemLp u_chart 2
      ((volume : Measure EuclN).restrict K) := by
    have h_restrict := h_global.restrict K
    have h_eq : ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)).restrict K =
        (volume : Measure EuclN).restrict K := by
      rw [Measure.restrict_restrict hK_meas]
      congr 1
      exact Set.inter_eq_self_of_subset_left hK_in
    rw [h_eq] at h_restrict
    exact h_restrict
  obtain ⟨c, _hc_pos, h_le⟩ :=
    chartPulledWeighted_le_volume_on_compact_aux
      (I := I) (M := M) (g := g) α hK_compact hK_meas hK_in
  have h_u_weighted_K : MemLp u_chart 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict K) :=
    h_global_K.of_measure_le_smul (c := ENNReal.ofReal c)
      ENNReal.ofReal_ne_top h_le
  have h_indicator_memLp_weighted :
      MemLp (K.indicator u_chart) 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)) := by
    rw [memLp_indicator_iff_restrict hK_meas]
    have h_double_restrict :
        ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α)).restrict K =
        (chartPulledWeightedMeasure (I := I) g α).restrict K := by
      rw [Measure.restrict_restrict hK_meas]
      congr 1
      exact Set.inter_eq_self_of_subset_left hK_in
    rw [h_double_restrict]
    exact h_u_weighted_K
  have h_absCont :
      (chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α) ≪
      (volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α) := by
    refine Measure.AbsolutelyContinuous.restrict ?_ _
    unfold chartPulledWeightedMeasure
    exact MeasureTheory.withDensity_absolutelyContinuous _ _
  have h_u_eq_ind_weighted :
      u_chart =ᵐ[(chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)] K.indicator u_chart :=
    h_absCont.ae_eq h_u_eq_ind
  exact (memLp_congr_ae h_u_eq_ind_weighted).mpr h_indicator_memLp_weighted

private noncomputable def iterated_u_chart
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g) (m : ℕ)
    (dirs : Fin m → Fin (Module.finrank ℝ E)) : EuclN → ℝ :=
  chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h m dirs

private noncomputable def iterated_weak_partial
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g) (m : ℕ)
    (dirs : Fin m → Fin (Module.finrank ℝ E))
    (i : Fin (Module.finrank ℝ E)) : EuclN → ℝ :=
  chosenWeakPartial' (d := Module.finrank ℝ E) 2 i
    (iterated_u_chart (I := I) (M := M) g α u_h m dirs)
    (chartTargetEuclid (I := I) (M := M) α)

omit [NeZero (Module.finrank ℝ E)] in
private lemma iterated_weak_partial_isWeakPartial
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g) (m : ℕ)
    (h_parent_m_plus_1 : MemWkp (d := Module.finrank ℝ E) (m + 1) 2
      (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
      (chartTargetEuclid (I := I) (M := M) α))
    (dirs : Fin m → Fin (Module.finrank ℝ E))
    (i : Fin (Module.finrank ℝ E)) :
    DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) i
      (iterated_weak_partial (I := I) (M := M) g α u_h m dirs i)
      (iterated_u_chart (I := I) (M := M) g α u_h m dirs)
      (chartTargetEuclid (I := I) (M := M) α) := by
  unfold iterated_weak_partial iterated_u_chart
  have h_memW1p :=
    chosenMthMixedPartialChartPushedU_memW1p_two
      (I := I) (M := M) g α u_h m h_parent_m_plus_1 dirs
  exact chosenWeakPartial'_isWeakPartial_of_mem h_memW1p i

omit [NeZero (Module.finrank ℝ E)] in
private lemma iterated_weak_partial_locally_memLp
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g) (m : ℕ)
    (h_parent_m_plus_2 : MemWkp (d := Module.finrank ℝ E) (m + 2) 2
      (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
      (chartTargetEuclid (I := I) (M := M) α))
    (dirs : Fin m → Fin (Module.finrank ℝ E))
    (i : Fin (Module.finrank ℝ E))
    {K : Set EuclN} (hK_compact : IsCompact K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    MemLp (iterated_weak_partial (I := I) (M := M) g α u_h m dirs i) 2
      ((volume : Measure EuclN).restrict K) := by
  classical
  unfold iterated_weak_partial iterated_u_chart
  have h_parent_m_plus_1 :
      MemWkp (d := Module.finrank ℝ E) (m + 1) 2
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
        (chartTargetEuclid (I := I) (M := M) α) :=
    MemWkp.le_of_le (by omega) h_parent_m_plus_2
  have h_u_memW1p :=
    chosenMthMixedPartialChartPushedU_memW1p_two
      (I := I) (M := M) g α u_h m h_parent_m_plus_1 dirs
  have h_global :
      MemLp (chosenWeakPartial' (d := Module.finrank ℝ E) 2 i
        (chosenMthMixedPartialChartPushedU
          (I := I) (M := M) g α u_h m dirs)
        (chartTargetEuclid (I := I) (M := M) α)) 2
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) :=
    chosenWeakPartial'_memLp_of_mem h_u_memW1p i
  have hK_meas : MeasurableSet K := hK_compact.isClosed.measurableSet
  have h_eq : ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)).restrict K =
        (volume : Measure EuclN).restrict K := by
    rw [Measure.restrict_restrict hK_meas]
    congr 1
    exact Set.inter_eq_self_of_subset_left hK_in
  rw [← h_eq]
  exact h_global.restrict K

noncomputable def iteratedChartBilinearH1ComplData
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g} {m : ℕ}
    (D_m : IteratedDiffChartBilinearData (I := I) (M := M) g α u_h m)
    (h_chart_H_m_plus_1 : MemWkp (d := Module.finrank ℝ E) (m + 1) 2
      (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
      (chartTargetEuclid (I := I) (M := M) α))
    (h_chart_H_m_plus_2 : MemWkp (d := Module.finrank ℝ E) (m + 2) 2
      (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
      (chartTargetEuclid (I := I) (M := M) α)) :
    ChartBilinearH1ComplData (I := I) (M := M) g α where
  u_chart := iterated_u_chart (I := I) (M := M) g α u_h m D_m.directions
  f_chart := D_m.diffChartForcing
  weak_partial :=
    iterated_weak_partial (I := I) (M := M) g α u_h m D_m.directions
  u_chart_memLp_weighted := by
    have h_parent_m :
        MemWkp (d := Module.finrank ℝ E) m 2
          (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
            ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
          (chartTargetEuclid (I := I) (M := M) α) :=
      MemWkp.le_of_le (by omega) h_chart_H_m_plus_1
    unfold iterated_u_chart
    exact chosenMthMixedPartialChartPushedU_memLp_weighted
      (I := I) (M := M) g α u_h m h_parent_m h_chart_H_m_plus_1 D_m.directions
  f_chart_memLp_weighted := D_m.fChartEff_memLp_weighted
  weak_partial_locally_memLp := fun i _K hK_compact hK_in =>
    iterated_weak_partial_locally_memLp
      (I := I) (M := M) g α u_h m h_chart_H_m_plus_2 D_m.directions i
      hK_compact hK_in
  weak_partial_isWeakPartial := fun i =>
    iterated_weak_partial_isWeakPartial
      (I := I) (M := M) g α u_h m h_chart_H_m_plus_1 D_m.directions i
  variational_identity := by
    classical
    intro ψ hψ hψ_cs hψ_supp
    have h_in := D_m.m_diff_variational_identity ψ hψ hψ_cs hψ_supp
    set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
    have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
    have hΩ_meas : MeasurableSet Ω := hΩ_open.measurableSet
    have h_schwarz_ae : ∀ i : Fin (Module.finrank ℝ E),
        chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h (m + 1)
          (Fin.cons i D_m.directions) =ᵐ[
          (volume : Measure EuclN).restrict Ω]
        chosenWeakPartial' (d := Module.finrank ℝ E) 2 i
          (chosenMthMixedPartialChartPushedU (I := I) (M := M)
            g α u_h m D_m.directions) Ω := fun i =>
      chosenMthMixedPartialChartPushedU_cons_eq_chosenWeakPartial_chosenMthMixed_ae
        (I := I) (M := M) g α u_h m D_m.directions i h_chart_H_m_plus_2
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
                iterated_weak_partial
                  (I := I) (M := M) g α u_h m D_m.directions i y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(volume : Measure EuclN) := by
      refine MeasureTheory.integral_congr_ae ?_
      have h_combined : ∀ᵐ y ∂((volume : Measure EuclN).restrict Ω),
          ∀ i : Fin (Module.finrank ℝ E),
            chosenMthMixedPartialChartPushedU (I := I) (M := M)
              g α u_h (m + 1) (Fin.cons i D_m.directions) y =
            iterated_weak_partial
              (I := I) (M := M) g α u_h m D_m.directions i y := by
        rw [ae_all_iff]
        intro i
        filter_upwards [h_schwarz_ae i] with y hy
        unfold iterated_weak_partial iterated_u_chart
        exact hy
      filter_upwards [h_combined] with y hy
      refine Finset.sum_congr rfl ?_
      intro i _hi
      refine Finset.sum_congr rfl ?_
      intro j _hj
      rw [hy i]
    rw [h_principal_eq] at h_in
    exact h_in

private lemma thickening_mono_of_lt
    {β : Type*} [PseudoEMetricSpace β]
    {r r' : ℝ} (hr_lt : r < r') (K : Set β) :
    Metric.thickening r K ⊆ Metric.thickening r' K := by
  intro y hy
  refine Metric.mem_thickening_iff_infEDist_lt.mpr ?_
  have h := Metric.mem_thickening_iff_infEDist_lt.mp hy
  exact lt_of_lt_of_le h
    (ENNReal.ofReal_le_ofReal hr_lt.le)

private lemma self_subset_thickening_of_pos
    {β : Type*} [PseudoEMetricSpace β]
    {r : ℝ} (hr_pos : 0 < r) (K : Set β) :
    K ⊆ Metric.thickening r K :=
  Metric.self_subset_thickening hr_pos K


theorem iteratedDerivedChartBilinear_memWkp_two_two_interior
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g} (m : ℕ)
    (D_m : IteratedDiffChartBilinearData (I := I) (M := M) g α u_h m)
    (h_chart_H_m_plus_1 : MemWkp (d := Module.finrank ℝ E) (m + 1) 2
      (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
      (chartTargetEuclid (I := I) (M := M) α))
    (h_chart_H_m_plus_2 : MemWkp (d := Module.finrank ℝ E) (m + 2) 2
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
    iteratedChartBilinearH1ComplData (I := I) (M := M) g α D_m
      h_chart_H_m_plus_1 h_chart_H_m_plus_2
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
  have hK_α_in_Ω'' : K_α ⊆ Ω'' :=
    self_subset_thickening_of_pos h_two_ε_pos K_α
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
    exact thickening_mono_of_lt (by linarith) K_α
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

end IteratedNirenbergInterior
end Laplacian
end Analysis
end DifferentialGeometry

end
