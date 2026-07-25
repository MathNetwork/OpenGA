import DifferentialGeometry.Analysis.Sobolev.Nirenberg.ChartBilinearDischarge.SubstitutionSmoothApprox


noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal Pointwise

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace SubstitutionDischargeIBPExpand

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Laplacian.ChartLocalLaplacian
open DifferentialGeometry.Analysis.Laplacian.ChartMeasureEquiv
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open DifferentialGeometry.Analysis.Sobolev.NirenbergStandardTest
open DifferentialGeometry.Analysis.Sobolev.NirenbergDiffQuotTestFunction
open DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction
open DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeSmoothApprox
open DifferentialGeometry.Analysis.Sobolev.SubstitutionNonSmoothChartBilinear

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

omit [NeZero (Module.finrank ℝ E)] in
theorem chart_bilinear_identity_h1_0_smooth_seq
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {K_0 : Set EuclN} (hK_0_compact : IsCompact K_0)
    (_hK_0_in : K_0 ⊆ chartTargetEuclid (I := I) (M := M) α)
    {η : EuclN → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_supp : HasCompactSupport η)
    (hη_supp_in_K_0 : tsupport η ⊆ K_0)
    (k : Fin (Module.finrank ℝ E))
    {R₀ : ℝ} {h : ℝ} (hh : h ≠ 0) (hh_le : |h| ≤ R₀)
    (h_thick : Metric.cthickening |h| K_0 ⊆
      chartTargetEuclid (I := I) (M := M) α)
    {u_seq : ℕ → EuclN → ℝ}
    (hu_seq_smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (u_seq n))
    (hu_seq_cs : ∀ n, HasCompactSupport (u_seq n)) :
    ∀ n,
      (∫ y in Metric.cthickening |h| K_0,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i j y *
                D.weak_partial i y *
                (fderiv ℝ
                  (standardNirenbergTest (d := Module.finrank ℝ E) k h η
                    (u_seq n)) y) (EuclideanSpace.single j 1))
          ∂(volume : Measure EuclN)) +
        (∫ y in Metric.cthickening |h| K_0,
          densityOnEuclid (I := I) g α y * D.u_chart y *
            standardNirenbergTest (d := Module.finrank ℝ E) k h η
              (u_seq n) y
          ∂(volume : Measure EuclN)) =
      ∫ y in Metric.cthickening |h| K_0,
        densityOnEuclid (I := I) g α y * D.f_chart y *
          standardNirenbergTest (d := Module.finrank ℝ E) k h η
            (u_seq n) y
        ∂(volume : Measure EuclN) := by
  classical
  have h_thick_compact : IsCompact (Metric.cthickening |h| K_0) :=
    cthickening_K_0_isCompact (E := E) hK_0_compact hh_le
  intro n
  obtain ⟨h_v_smooth, h_v_cs⟩ :=
    standardNirenbergTest_smooth_seq hη hη_supp k hh hh_le
      hu_seq_smooth hu_seq_cs n
  have h_v_supp : tsupport (standardNirenbergTest (d := Module.finrank ℝ E)
      k h η (u_seq n)) ⊆ Metric.cthickening |h| K_0 :=
    standardNirenbergTest_tsupport_in_thickening (E := E) k h hη_supp
      hη_supp_in_K_0 (u_seq n)
  set ψ : EuclN → ℝ := standardNirenbergTest (d := Module.finrank ℝ E)
    k h η (u_seq n) with hψ_def
  set weak_partial_ψ : Fin (Module.finrank ℝ E) → EuclN → ℝ :=
    fun j x => (fderiv ℝ ψ x) (EuclideanSpace.single j 1) with hwp_def
  have hψ_lp : MemLp ψ 2
      ((volume : Measure EuclN).restrict (Metric.cthickening |h| K_0)) :=
    (h_v_smooth.continuous.memLp_of_hasCompactSupport h_v_cs).restrict _
  have hψ_grad_lp : ∀ j : Fin (Module.finrank ℝ E),
      MemLp (weak_partial_ψ j) 2
        ((volume : Measure EuclN).restrict (Metric.cthickening |h| K_0)) := by
    intro j
    have h_top_ne_zero : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by decide
    have h_cont : Continuous (weak_partial_ψ j) := by
      have h_fderiv_cont : Continuous (fderiv ℝ ψ) :=
        h_v_smooth.continuous_fderiv h_top_ne_zero
      exact h_fderiv_cont.clm_apply continuous_const
    have h_cs : HasCompactSupport (weak_partial_ψ j) :=
      h_v_cs.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single j 1)
    exact (h_cont.memLp_of_hasCompactSupport h_cs).restrict _
  set ψ_seq : ℕ → EuclN → ℝ := fun _ => ψ with hψseq_def
  have hψ_seq_smooth : ∀ m, ContDiff ℝ (⊤ : ℕ∞) (ψ_seq m) := fun _ => h_v_smooth
  have hψ_seq_cs : ∀ m, HasCompactSupport (ψ_seq m) := fun _ => h_v_cs
  have hψ_seq_supp : ∀ m, tsupport (ψ_seq m) ⊆ Metric.cthickening |h| K_0 :=
    fun _ => h_v_supp
  have hψ_seq_l2 :
      Tendsto (fun m => eLpNorm (fun x => ψ_seq m x - ψ x) 2
        ((volume : Measure EuclN).restrict (Metric.cthickening |h| K_0)))
        atTop (𝓝 0) := by
    have h_eq : (fun m : ℕ => eLpNorm (fun x => ψ_seq m x - ψ x) 2
        ((volume : Measure EuclN).restrict (Metric.cthickening |h| K_0))) =
        (fun _ : ℕ => (0 : ℝ≥0∞)) := by
      funext m
      have h_fun_eq : (fun x => ψ_seq m x - ψ x) = (fun _ : EuclN => (0 : ℝ)) := by
        funext x
        change ψ x - ψ x = 0
        ring
      rw [h_fun_eq]
      simp
    rw [h_eq]
    exact tendsto_const_nhds
  have hψ_seq_grad_l2 : ∀ j : Fin (Module.finrank ℝ E),
      Tendsto (fun m => eLpNorm
        (fun x => (fderiv ℝ (ψ_seq m) x) (EuclideanSpace.single j 1) -
          weak_partial_ψ j x) 2
        ((volume : Measure EuclN).restrict (Metric.cthickening |h| K_0)))
        atTop (𝓝 0) := by
    intro j
    have h_eq : (fun m : ℕ => eLpNorm
        (fun x => (fderiv ℝ (ψ_seq m) x) (EuclideanSpace.single j 1) -
          weak_partial_ψ j x) 2
        ((volume : Measure EuclN).restrict (Metric.cthickening |h| K_0))) =
        (fun _ : ℕ => (0 : ℝ≥0∞)) := by
      funext m
      have h_fun_eq : (fun x => (fderiv ℝ (ψ_seq m) x)
          (EuclideanSpace.single j 1) - weak_partial_ψ j x) =
          (fun _ : EuclN => (0 : ℝ)) := by
        funext x
        change (fderiv ℝ ψ x) (EuclideanSpace.single j 1) -
          (fderiv ℝ ψ x) (EuclideanSpace.single j 1) = 0
        ring
      rw [h_fun_eq]
      simp
    rw [h_eq]
    exact tendsto_const_nhds
  exact chart_bilinear_identity_h1_0 (I := I) (M := M) D
    h_thick_compact h_thick ψ weak_partial_ψ hψ_lp hψ_grad_lp ψ_seq
    hψ_seq_smooth hψ_seq_cs hψ_seq_supp hψ_seq_l2 hψ_seq_grad_l2


omit [NeZero (Module.finrank ℝ E)] in
theorem variational_identity_at_v_h
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {K_0 : Set EuclN} (hK_0_compact : IsCompact K_0)
    (_hK_0_in : K_0 ⊆ chartTargetEuclid (I := I) (M := M) α)
    {η : EuclN → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_supp : HasCompactSupport η)
    (_hη_supp_in_K_0 : tsupport η ⊆ K_0)
    (k : Fin (Module.finrank ℝ E))
    {R₀ : ℝ} {h : ℝ} (hh : h ≠ 0) (hh_le : |h| ≤ R₀)
    (h_thick : Metric.cthickening |h| K_0 ⊆
      chartTargetEuclid (I := I) (M := M) α)
    (weak_partial_v_h : Fin (Module.finrank ℝ E) → EuclN → ℝ)
    (hv_h_lp : MemLp (standardNirenbergTest (d := Module.finrank ℝ E)
        k h η D.u_chart) 2
      ((volume : Measure EuclN).restrict (Metric.cthickening |h| K_0)))
    (hv_h_grad_lp : ∀ j : Fin (Module.finrank ℝ E),
      MemLp (weak_partial_v_h j) 2
        ((volume : Measure EuclN).restrict (Metric.cthickening |h| K_0)))
    (u_seq : ℕ → EuclN → ℝ)
    (hu_seq_smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (u_seq n))
    (hu_seq_cs : ∀ n, HasCompactSupport (u_seq n))
    (h_v_seq_supp : ∀ n,
      tsupport (standardNirenbergTest (d := Module.finrank ℝ E)
        k h η (u_seq n)) ⊆ Metric.cthickening |h| K_0)
    (h_v_seq_l2 :
      Tendsto (fun n => eLpNorm (fun x =>
        standardNirenbergTest (d := Module.finrank ℝ E) k h η (u_seq n) x -
        standardNirenbergTest (d := Module.finrank ℝ E) k h η D.u_chart x) 2
        ((volume : Measure EuclN).restrict (Metric.cthickening |h| K_0)))
        atTop (𝓝 0))
    (h_v_seq_grad_l2 : ∀ j : Fin (Module.finrank ℝ E),
      Tendsto (fun n => eLpNorm
        (fun x => (fderiv ℝ
          (standardNirenbergTest (d := Module.finrank ℝ E) k h η
            (u_seq n)) x) (EuclideanSpace.single j 1) -
          weak_partial_v_h j x) 2
        ((volume : Measure EuclN).restrict (Metric.cthickening |h| K_0)))
        atTop (𝓝 0)) :
    (∫ y in Metric.cthickening |h| K_0,
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            weightedInvGramOnEuclid (I := I) g α i j y *
              D.weak_partial i y *
              weak_partial_v_h j y)
        ∂(volume : Measure EuclN)) +
      (∫ y in Metric.cthickening |h| K_0,
        densityOnEuclid (I := I) g α y * D.u_chart y *
          standardNirenbergTest (d := Module.finrank ℝ E) k h η D.u_chart y
        ∂(volume : Measure EuclN)) =
      ∫ y in Metric.cthickening |h| K_0,
        densityOnEuclid (I := I) g α y * D.f_chart y *
          standardNirenbergTest (d := Module.finrank ℝ E) k h η D.u_chart y
        ∂(volume : Measure EuclN) := by
  classical
  have h_thick_compact : IsCompact (Metric.cthickening |h| K_0) :=
    cthickening_K_0_isCompact (E := E) hK_0_compact hh_le
  set v_h : EuclN → ℝ := standardNirenbergTest (d := Module.finrank ℝ E)
    k h η D.u_chart with hvh_def
  set v_h_seq : ℕ → EuclN → ℝ := fun n =>
    standardNirenbergTest (d := Module.finrank ℝ E) k h η (u_seq n)
    with hvhseq_def
  have h_v_seq_smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (v_h_seq n) := fun n =>
    (standardNirenbergTest_smooth_seq hη hη_supp k hh hh_le
      hu_seq_smooth hu_seq_cs n).1
  have h_v_seq_cs : ∀ n, HasCompactSupport (v_h_seq n) := fun n =>
    (standardNirenbergTest_smooth_seq hη hη_supp k hh hh_le
      hu_seq_smooth hu_seq_cs n).2
  exact chart_bilinear_identity_h1_0 (I := I) (M := M) D
    h_thick_compact h_thick v_h weak_partial_v_h hv_h_lp hv_h_grad_lp
    v_h_seq h_v_seq_smooth h_v_seq_cs h_v_seq_supp h_v_seq_l2
    h_v_seq_grad_l2


omit [NeZero (Module.finrank ℝ E)] in
theorem variational_identity_v_h_expanded
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {K_0 : Set EuclN}
    {η : EuclN → ℝ}
    (k : Fin (Module.finrank ℝ E))
    {_R₀ : ℝ} {h : ℝ}
    (weak_partial_v_h : Fin (Module.finrank ℝ E) → EuclN → ℝ)
    (h_var_id_at_v_h :
      (∫ y in Metric.cthickening |h| K_0,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i j y *
                D.weak_partial i y *
                weak_partial_v_h j y)
          ∂(volume : Measure EuclN)) +
        (∫ y in Metric.cthickening |h| K_0,
          densityOnEuclid (I := I) g α y * D.u_chart y *
            standardNirenbergTest (d := Module.finrank ℝ E) k h η
              D.u_chart y
          ∂(volume : Measure EuclN)) =
        ∫ y in Metric.cthickening |h| K_0,
          densityOnEuclid (I := I) g α y * D.f_chart y *
            standardNirenbergTest (d := Module.finrank ℝ E) k h η
              D.u_chart y
          ∂(volume : Measure EuclN))
    (h_weak_partial_eq : ∀ j : Fin (Module.finrank ℝ E), ∀ᵐ y
        ∂((volume : Measure EuclN).restrict (Metric.cthickening |h| K_0)),
      weak_partial_v_h j y =
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k (-h)
          (fun z => (η z) ^ 2 *
            DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h (D.weak_partial j) z +
            2 * η z * (fderiv ℝ η z) (EuclideanSpace.single j 1) *
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h D.u_chart z) y) :
    (∫ y in Metric.cthickening |h| K_0,
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            weightedInvGramOnEuclid (I := I) g α i j y *
              D.weak_partial i y *
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k (-h)
                (fun z => (η z) ^ 2 *
                  DifferentialGeometry.Analysis.Sobolev.diffQuot
                    (d := Module.finrank ℝ E) k h (D.weak_partial j) z +
                  2 * η z * (fderiv ℝ η z) (EuclideanSpace.single j 1) *
                    DifferentialGeometry.Analysis.Sobolev.diffQuot
                      (d := Module.finrank ℝ E) k h D.u_chart z) y)
        ∂(volume : Measure EuclN)) +
      (∫ y in Metric.cthickening |h| K_0,
        densityOnEuclid (I := I) g α y * D.u_chart y *
          standardNirenbergTest (d := Module.finrank ℝ E) k h η D.u_chart y
        ∂(volume : Measure EuclN)) =
      ∫ y in Metric.cthickening |h| K_0,
        densityOnEuclid (I := I) g α y * D.f_chart y *
          standardNirenbergTest (d := Module.finrank ℝ E) k h η D.u_chart y
        ∂(volume : Measure EuclN) := by
  classical
  have h_principal_eq :
      ∫ y in Metric.cthickening |h| K_0,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i j y *
                D.weak_partial i y *
                weak_partial_v_h j y)
          ∂(volume : Measure EuclN) =
        ∫ y in Metric.cthickening |h| K_0,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i j y *
                D.weak_partial i y *
                DifferentialGeometry.Analysis.Sobolev.diffQuot
                  (d := Module.finrank ℝ E) k (-h)
                  (fun z => (η z) ^ 2 *
                    DifferentialGeometry.Analysis.Sobolev.diffQuot
                      (d := Module.finrank ℝ E) k h (D.weak_partial j) z +
                    2 * η z * (fderiv ℝ η z) (EuclideanSpace.single j 1) *
                      DifferentialGeometry.Analysis.Sobolev.diffQuot
                        (d := Module.finrank ℝ E) k h D.u_chart z) y)
          ∂(volume : Measure EuclN) := by
    refine integral_congr_ae ?_
    have h_all : ∀ j : Fin (Module.finrank ℝ E), ∀ᵐ y
        ∂((volume : Measure EuclN).restrict (Metric.cthickening |h| K_0)),
      weak_partial_v_h j y =
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k (-h)
          (fun z => (η z) ^ 2 *
            DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h (D.weak_partial j) z +
            2 * η z * (fderiv ℝ η z) (EuclideanSpace.single j 1) *
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h D.u_chart z) y :=
      h_weak_partial_eq
    have h_combined : ∀ᵐ y
        ∂((volume : Measure EuclN).restrict (Metric.cthickening |h| K_0)),
      ∀ j : Fin (Module.finrank ℝ E), weak_partial_v_h j y =
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k (-h)
          (fun z => (η z) ^ 2 *
            DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h (D.weak_partial j) z +
            2 * η z * (fderiv ℝ η z) (EuclideanSpace.single j 1) *
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h D.u_chart z) y := by
      rw [ae_all_iff]
      exact h_all
    filter_upwards [h_combined] with y hy
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hy j]
  rw [← h_principal_eq]
  exact h_var_id_at_v_h


omit [NeZero (Module.finrank ℝ E)] in
theorem variational_identity_after_ibp
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {K_0 : Set EuclN} (_hK_0_compact : IsCompact K_0)
    (_hK_0_in : K_0 ⊆ chartTargetEuclid (I := I) (M := M) α)
    {η : EuclN → ℝ} (_hη : ContDiff ℝ (⊤ : ℕ∞) η) (_hη_supp : HasCompactSupport η)
    (_hη_supp_in_K_0 : tsupport η ⊆ K_0)
    (k : Fin (Module.finrank ℝ E))
    {R₀ : ℝ} {h : ℝ} (_hh : h ≠ 0) (_hh_le : |h| ≤ R₀)
    (_h_thick : Metric.cthickening |h| K_0 ⊆
      chartTargetEuclid (I := I) (M := M) α)
    (h_expanded :
      (∫ y in Metric.cthickening |h| K_0,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i j y *
                D.weak_partial i y *
                DifferentialGeometry.Analysis.Sobolev.diffQuot
                  (d := Module.finrank ℝ E) k (-h)
                  (fun z => (η z) ^ 2 *
                    DifferentialGeometry.Analysis.Sobolev.diffQuot
                      (d := Module.finrank ℝ E) k h (D.weak_partial j) z +
                    2 * η z * (fderiv ℝ η z) (EuclideanSpace.single j 1) *
                      DifferentialGeometry.Analysis.Sobolev.diffQuot
                        (d := Module.finrank ℝ E) k h D.u_chart z) y)
          ∂(volume : Measure EuclN)) +
        (∫ y in Metric.cthickening |h| K_0,
          densityOnEuclid (I := I) g α y * D.u_chart y *
            standardNirenbergTest (d := Module.finrank ℝ E) k h η
              D.u_chart y
          ∂(volume : Measure EuclN)) =
        ∫ y in Metric.cthickening |h| K_0,
          densityOnEuclid (I := I) g α y * D.f_chart y *
            standardNirenbergTest (d := Module.finrank ℝ E) k h η
              D.u_chart y
          ∂(volume : Measure EuclN))
    (h_ibp_per_ij : ∀ i j : Fin (Module.finrank ℝ E),
      ∫ y in Metric.cthickening |h| K_0,
        weightedInvGramOnEuclid (I := I) g α i j y *
          D.weak_partial i y *
          DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k (-h)
            (fun z => (η z) ^ 2 *
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h (D.weak_partial j) z +
              2 * η z * (fderiv ℝ η z) (EuclideanSpace.single j 1) *
                DifferentialGeometry.Analysis.Sobolev.diffQuot
                  (d := Module.finrank ℝ E) k h D.u_chart z) y
        ∂(volume : Measure EuclN) =
      - ∫ y in Metric.cthickening |h| K_0,
          DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h
            (fun z => weightedInvGramOnEuclid (I := I) g α i j z *
              D.weak_partial i z) y *
          ((η y) ^ 2 *
            DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h (D.weak_partial j) y +
            2 * η y * (fderiv ℝ η y) (EuclideanSpace.single j 1) *
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h D.u_chart y)
        ∂(volume : Measure EuclN))
    (h_principal_integrable : ∀ i j : Fin (Module.finrank ℝ E),
      Integrable (fun y =>
        weightedInvGramOnEuclid (I := I) g α i j y *
          D.weak_partial i y *
          DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k (-h)
            (fun z => (η z) ^ 2 *
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h (D.weak_partial j) z +
              2 * η z * (fderiv ℝ η z) (EuclideanSpace.single j 1) *
                DifferentialGeometry.Analysis.Sobolev.diffQuot
                  (d := Module.finrank ℝ E) k h D.u_chart z) y)
        ((volume : Measure EuclN).restrict (Metric.cthickening |h| K_0)))
    (h_principal_integrable_after : ∀ i j : Fin (Module.finrank ℝ E),
      Integrable (fun y =>
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h
          (fun z => weightedInvGramOnEuclid (I := I) g α i j z *
            D.weak_partial i z) y *
        ((η y) ^ 2 *
          DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h (D.weak_partial j) y +
          2 * η y * (fderiv ℝ η y) (EuclideanSpace.single j 1) *
            DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h D.u_chart y))
        ((volume : Measure EuclN).restrict (Metric.cthickening |h| K_0))) :
    -(∫ y in Metric.cthickening |h| K_0,
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h
              (fun z => weightedInvGramOnEuclid (I := I) g α i j z *
                D.weak_partial i z) y *
            ((η y) ^ 2 *
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h (D.weak_partial j) y +
              2 * η y * (fderiv ℝ η y) (EuclideanSpace.single j 1) *
                DifferentialGeometry.Analysis.Sobolev.diffQuot
                  (d := Module.finrank ℝ E) k h D.u_chart y))
        ∂(volume : Measure EuclN)) +
      (∫ y in Metric.cthickening |h| K_0,
        densityOnEuclid (I := I) g α y * D.u_chart y *
          standardNirenbergTest (d := Module.finrank ℝ E) k h η D.u_chart y
        ∂(volume : Measure EuclN)) =
      ∫ y in Metric.cthickening |h| K_0,
        densityOnEuclid (I := I) g α y * D.f_chart y *
          standardNirenbergTest (d := Module.finrank ℝ E) k h η D.u_chart y
        ∂(volume : Measure EuclN) := by
  classical
  have h_int_swap_before :
      ∫ y in Metric.cthickening |h| K_0,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i j y *
                D.weak_partial i y *
                DifferentialGeometry.Analysis.Sobolev.diffQuot
                  (d := Module.finrank ℝ E) k (-h)
                  (fun z => (η z) ^ 2 *
                    DifferentialGeometry.Analysis.Sobolev.diffQuot
                      (d := Module.finrank ℝ E) k h (D.weak_partial j) z +
                    2 * η z * (fderiv ℝ η z) (EuclideanSpace.single j 1) *
                      DifferentialGeometry.Analysis.Sobolev.diffQuot
                        (d := Module.finrank ℝ E) k h D.u_chart z) y)
          ∂(volume : Measure EuclN) =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ∫ y in Metric.cthickening |h| K_0,
            weightedInvGramOnEuclid (I := I) g α i j y *
              D.weak_partial i y *
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k (-h)
                (fun z => (η z) ^ 2 *
                  DifferentialGeometry.Analysis.Sobolev.diffQuot
                    (d := Module.finrank ℝ E) k h (D.weak_partial j) z +
                  2 * η z * (fderiv ℝ η z) (EuclideanSpace.single j 1) *
                    DifferentialGeometry.Analysis.Sobolev.diffQuot
                      (d := Module.finrank ℝ E) k h D.u_chart z) y
            ∂(volume : Measure EuclN) := by
    rw [integral_finset_sum]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_finset_sum]
      intro j _
      exact h_principal_integrable i j
    · intro i _
      exact integrable_finset_sum _ (fun j _ => h_principal_integrable i j)
  have h_int_swap_after :
      ∫ y in Metric.cthickening |h| K_0,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h
                (fun z => weightedInvGramOnEuclid (I := I) g α i j z *
                  D.weak_partial i z) y *
              ((η y) ^ 2 *
                DifferentialGeometry.Analysis.Sobolev.diffQuot
                  (d := Module.finrank ℝ E) k h (D.weak_partial j) y +
                2 * η y * (fderiv ℝ η y) (EuclideanSpace.single j 1) *
                  DifferentialGeometry.Analysis.Sobolev.diffQuot
                    (d := Module.finrank ℝ E) k h D.u_chart y))
          ∂(volume : Measure EuclN) =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ∫ y in Metric.cthickening |h| K_0,
            DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h
              (fun z => weightedInvGramOnEuclid (I := I) g α i j z *
                D.weak_partial i z) y *
            ((η y) ^ 2 *
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h (D.weak_partial j) y +
              2 * η y * (fderiv ℝ η y) (EuclideanSpace.single j 1) *
                DifferentialGeometry.Analysis.Sobolev.diffQuot
                  (d := Module.finrank ℝ E) k h D.u_chart y)
            ∂(volume : Measure EuclN) := by
    rw [integral_finset_sum]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_finset_sum]
      intro j _
      exact h_principal_integrable_after i j
    · intro i _
      exact integrable_finset_sum _ (fun j _ => h_principal_integrable_after i j)
  have h_per_ij_eq :
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ∫ y in Metric.cthickening |h| K_0,
            weightedInvGramOnEuclid (I := I) g α i j y *
              D.weak_partial i y *
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k (-h)
                (fun z => (η z) ^ 2 *
                  DifferentialGeometry.Analysis.Sobolev.diffQuot
                    (d := Module.finrank ℝ E) k h (D.weak_partial j) z +
                  2 * η z * (fderiv ℝ η z) (EuclideanSpace.single j 1) *
                    DifferentialGeometry.Analysis.Sobolev.diffQuot
                      (d := Module.finrank ℝ E) k h D.u_chart z) y
            ∂(volume : Measure EuclN)) =
      - ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            ∫ y in Metric.cthickening |h| K_0,
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h
                (fun z => weightedInvGramOnEuclid (I := I) g α i j z *
                  D.weak_partial i z) y *
              ((η y) ^ 2 *
                DifferentialGeometry.Analysis.Sobolev.diffQuot
                  (d := Module.finrank ℝ E) k h (D.weak_partial j) y +
                2 * η y * (fderiv ℝ η y) (EuclideanSpace.single j 1) *
                  DifferentialGeometry.Analysis.Sobolev.diffQuot
                    (d := Module.finrank ℝ E) k h D.u_chart y)
              ∂(volume : Measure EuclN) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact h_ibp_per_ij i j
  rw [h_int_swap_before, h_per_ij_eq, ← h_int_swap_after] at h_expanded
  exact h_expanded


omit [NeZero (Module.finrank ℝ E)] in
theorem variational_identity_after_product_rule
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {K_0 : Set EuclN} (_hK_0_compact : IsCompact K_0)
    (_hK_0_in : K_0 ⊆ chartTargetEuclid (I := I) (M := M) α)
    {η : EuclN → ℝ} (_hη : ContDiff ℝ (⊤ : ℕ∞) η) (_hη_supp : HasCompactSupport η)
    (_hη_supp_in_K_0 : tsupport η ⊆ K_0)
    (k : Fin (Module.finrank ℝ E))
    {R₀ : ℝ} {h : ℝ} (_hh : h ≠ 0) (_hh_le : |h| ≤ R₀)
    (_h_thick : Metric.cthickening |h| K_0 ⊆
      chartTargetEuclid (I := I) (M := M) α)
    (h_after_ibp :
      -(∫ y in Metric.cthickening |h| K_0,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h
                (fun z => weightedInvGramOnEuclid (I := I) g α i j z *
                  D.weak_partial i z) y *
              ((η y) ^ 2 *
                DifferentialGeometry.Analysis.Sobolev.diffQuot
                  (d := Module.finrank ℝ E) k h (D.weak_partial j) y +
                2 * η y * (fderiv ℝ η y) (EuclideanSpace.single j 1) *
                  DifferentialGeometry.Analysis.Sobolev.diffQuot
                    (d := Module.finrank ℝ E) k h D.u_chart y))
          ∂(volume : Measure EuclN)) +
        (∫ y in Metric.cthickening |h| K_0,
          densityOnEuclid (I := I) g α y * D.u_chart y *
            standardNirenbergTest (d := Module.finrank ℝ E) k h η D.u_chart y
          ∂(volume : Measure EuclN)) =
        ∫ y in Metric.cthickening |h| K_0,
          densityOnEuclid (I := I) g α y * D.f_chart y *
            standardNirenbergTest (d := Module.finrank ℝ E) k h η D.u_chart y
          ∂(volume : Measure EuclN))
    (h_principal_in_K_0_eq :
      ∫ y in Metric.cthickening |h| K_0,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h
                (fun z => weightedInvGramOnEuclid (I := I) g α i j z *
                  D.weak_partial i z) y *
              ((η y) ^ 2 *
                DifferentialGeometry.Analysis.Sobolev.diffQuot
                  (d := Module.finrank ℝ E) k h (D.weak_partial j) y +
                2 * η y * (fderiv ℝ η y) (EuclideanSpace.single j 1) *
                  DifferentialGeometry.Analysis.Sobolev.diffQuot
                    (d := Module.finrank ℝ E) k h D.u_chart y))
          ∂(volume : Measure EuclN) =
      principalTerm_chartBilinear (I := I) (M := M) D K_0 η k h
        + cross_1_term_chartBilinear (I := I) (M := M) D K_0 η k h
        + cross_2_term_chartBilinear (I := I) (M := M) D K_0 η k h
        + cross_3_term_chartBilinear (I := I) (M := M) D K_0 η k h)
    (h_c_term_eq :
      ∫ y in Metric.cthickening |h| K_0,
        densityOnEuclid (I := I) g α y * D.u_chart y *
          standardNirenbergTest (d := Module.finrank ℝ E) k h η D.u_chart y
      ∂(volume : Measure EuclN) =
      c_term_chartBilinear (I := I) (M := M) D K_0 η k h)
    (h_f_term_eq :
      ∫ y in Metric.cthickening |h| K_0,
        densityOnEuclid (I := I) g α y * D.f_chart y *
          standardNirenbergTest (d := Module.finrank ℝ E) k h η D.u_chart y
      ∂(volume : Measure EuclN) =
      f_term_chartBilinear (I := I) (M := M) D K_0 η k h) :
    principalTerm_chartBilinear (I := I) (M := M) D K_0 η k h
      + cross_1_term_chartBilinear (I := I) (M := M) D K_0 η k h
      + cross_2_term_chartBilinear (I := I) (M := M) D K_0 η k h
      + cross_3_term_chartBilinear (I := I) (M := M) D K_0 η k h
      + f_term_chartBilinear (I := I) (M := M) D K_0 η k h
      = c_term_chartBilinear (I := I) (M := M) D K_0 η k h := by
  classical
  rw [h_principal_in_K_0_eq, h_c_term_eq, h_f_term_eq] at h_after_ibp
  linarith

end SubstitutionDischargeIBPExpand
end Sobolev
end Analysis
end DifferentialGeometry
