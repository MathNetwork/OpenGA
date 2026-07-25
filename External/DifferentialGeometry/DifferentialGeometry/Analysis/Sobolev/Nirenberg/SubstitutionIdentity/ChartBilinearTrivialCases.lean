import DifferentialGeometry.Analysis.Sobolev.Nirenberg.ChartBilinearDischarge.SubstitutionIBPExpand
import DifferentialGeometry.Analysis.Sobolev.Nirenberg.ChartBilinearDischarge.SubstitutionChartBilinear


noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal Pointwise

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace SubstitutionDischargeFinal

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
open DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeIBPExpand
open DifferentialGeometry.Analysis.Sobolev.SubstitutionNonSmoothChartBilinear

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

omit [NeZero (Module.finrank ℝ E)] in
private lemma principalTerm_chartBilinear_zero_h
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    (K_0 : Set EuclN) (η : EuclN → ℝ)
    (k : Fin (Module.finrank ℝ E)) :
    principalTerm_chartBilinear (I := I) (M := M) D K_0 η k 0 = 0 := by
  unfold principalTerm_chartBilinear
  have h_eq : (fun x : EuclN =>
    (∑ i : Fin (Module.finrank ℝ E),
      ∑ j : Fin (Module.finrank ℝ E),
        DifferentialGeometry.Analysis.Sobolev.translate
          (d := Module.finrank ℝ E) k 0
          (fun y => weightedInvGramOnEuclid (I := I) g α i j y) x *
        (η x) ^ 2 *
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k 0 (D.weak_partial i) x *
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k 0 (D.weak_partial j) x)) =
      (fun _ => (0 : ℝ)) := by
    funext x
    refine Finset.sum_eq_zero (fun i _ => ?_)
    refine Finset.sum_eq_zero (fun j _ => ?_)
    have h_dq : DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k 0 (D.weak_partial i) x = 0 := by
      simp [DifferentialGeometry.Analysis.Sobolev.diffQuot]
    rw [h_dq]; ring
  rw [h_eq]
  simp

omit [NeZero (Module.finrank ℝ E)] in
private lemma cross_1_term_chartBilinear_zero_h
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    (K_0 : Set EuclN) (η : EuclN → ℝ)
    (k : Fin (Module.finrank ℝ E)) :
    cross_1_term_chartBilinear (I := I) (M := M) D K_0 η k 0 = 0 := by
  unfold cross_1_term_chartBilinear
  refine Finset.sum_eq_zero (fun i _ => ?_)
  refine Finset.sum_eq_zero (fun j _ => ?_)
  have h_eq : (fun x : EuclN =>
      2 *
        DifferentialGeometry.Analysis.Sobolev.translate
          (d := Module.finrank ℝ E) k 0
          (fun y => weightedInvGramOnEuclid (I := I) g α i j y) x *
        (η x) *
        ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k 0 (D.weak_partial i) x *
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k 0 D.u_chart x) = (fun _ => (0 : ℝ)) := by
    funext x
    have h_dq : DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k 0 (D.weak_partial i) x = 0 := by
      simp [DifferentialGeometry.Analysis.Sobolev.diffQuot]
    rw [h_dq]; ring
  rw [h_eq]
  simp

omit [NeZero (Module.finrank ℝ E)] in
private lemma cross_2_term_chartBilinear_zero_h
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    (K_0 : Set EuclN) (η : EuclN → ℝ)
    (k : Fin (Module.finrank ℝ E)) :
    cross_2_term_chartBilinear (I := I) (M := M) D K_0 η k 0 = 0 := by
  unfold cross_2_term_chartBilinear
  refine Finset.sum_eq_zero (fun i _ => ?_)
  refine Finset.sum_eq_zero (fun j _ => ?_)
  have h_eq : (fun x : EuclN =>
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k 0
        (fun y => weightedInvGramOnEuclid (I := I) g α i j y) x *
      (η x) ^ 2 *
      D.weak_partial i x *
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k 0 (D.weak_partial j) x) =
      (fun _ => (0 : ℝ)) := by
    funext x
    have h_dq : DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k 0
        (fun y => weightedInvGramOnEuclid (I := I) g α i j y) x = 0 := by
      simp [DifferentialGeometry.Analysis.Sobolev.diffQuot]
    rw [h_dq]; ring
  rw [h_eq]
  simp

omit [NeZero (Module.finrank ℝ E)] in
private lemma cross_3_term_chartBilinear_zero_h
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    (K_0 : Set EuclN) (η : EuclN → ℝ)
    (k : Fin (Module.finrank ℝ E)) :
    cross_3_term_chartBilinear (I := I) (M := M) D K_0 η k 0 = 0 := by
  unfold cross_3_term_chartBilinear
  refine Finset.sum_eq_zero (fun i _ => ?_)
  refine Finset.sum_eq_zero (fun j _ => ?_)
  have h_eq : (fun x : EuclN =>
      2 *
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k 0
          (fun y => weightedInvGramOnEuclid (I := I) g α i j y) x *
        (η x) *
        ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
        D.weak_partial i x *
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k 0 D.u_chart x) = (fun _ => (0 : ℝ)) := by
    funext x
    have h_dq : DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k 0 D.u_chart x = 0 := by
      simp [DifferentialGeometry.Analysis.Sobolev.diffQuot]
    rw [h_dq]; ring
  rw [h_eq]
  simp

omit [NeZero (Module.finrank ℝ E)] in
private lemma c_term_chartBilinear_zero_h
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    (K_0 : Set EuclN) (η : EuclN → ℝ)
    (k : Fin (Module.finrank ℝ E)) :
    c_term_chartBilinear (I := I) (M := M) D K_0 η k 0 = 0 := by
  unfold c_term_chartBilinear
  have h_eq : (fun x : EuclN =>
      densityOnEuclid (I := I) g α x * D.u_chart x *
        standardNirenbergTest
          (d := Module.finrank ℝ E) k 0 η D.u_chart x) = (fun _ => (0 : ℝ)) := by
    funext x
    have h_test : standardNirenbergTest
        (d := Module.finrank ℝ E) k 0 η D.u_chart x = 0 := by
      have := standardNirenbergTest_zero_h
        (d := Module.finrank ℝ E) k η D.u_chart
      exact congrArg (fun f : EuclN → ℝ => f x) this
    rw [h_test]; ring
  rw [h_eq]
  simp

omit [NeZero (Module.finrank ℝ E)] in
private lemma f_term_chartBilinear_zero_h
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    (K_0 : Set EuclN) (η : EuclN → ℝ)
    (k : Fin (Module.finrank ℝ E)) :
    f_term_chartBilinear (I := I) (M := M) D K_0 η k 0 = 0 := by
  unfold f_term_chartBilinear
  have h_eq : (fun x : EuclN =>
      densityOnEuclid (I := I) g α x * D.f_chart x *
        standardNirenbergTest
          (d := Module.finrank ℝ E) k 0 η D.u_chart x) = (fun _ => (0 : ℝ)) := by
    funext x
    have h_test : standardNirenbergTest
        (d := Module.finrank ℝ E) k 0 η D.u_chart x = 0 := by
      have := standardNirenbergTest_zero_h
        (d := Module.finrank ℝ E) k η D.u_chart
      exact congrArg (fun f : EuclN → ℝ => f x) this
    rw [h_test]; ring
  rw [h_eq]
  simp

omit [NeZero (Module.finrank ℝ E)] in
private lemma chartBilinear_substitution_identity_zero_h
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    (K_0 : Set EuclN) (η : EuclN → ℝ)
    (k : Fin (Module.finrank ℝ E)) :
    chartBilinear_LHS (I := I) (M := M) D K_0 η k 0 =
    chartBilinear_RHS (I := I) (M := M) D K_0 η k 0 := by
  unfold chartBilinear_LHS chartBilinear_RHS
  rw [principalTerm_chartBilinear_zero_h, cross_1_term_chartBilinear_zero_h,
    cross_2_term_chartBilinear_zero_h, cross_3_term_chartBilinear_zero_h,
    f_term_chartBilinear_zero_h, c_term_chartBilinear_zero_h]
  ring

omit [NeZero (Module.finrank ℝ E)] in
private lemma chartBilinear_substitution_identity_K_0_empty
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {K_0 : Set EuclN} (hK_0_empty : K_0 = ∅)
    (η : EuclN → ℝ)
    (hη_supp_in_K_0 : tsupport η ⊆ K_0)
    (k : Fin (Module.finrank ℝ E)) (h : ℝ) :
    chartBilinear_LHS (I := I) (M := M) D K_0 η k h =
    chartBilinear_RHS (I := I) (M := M) D K_0 η k h := by
  classical
  have hη_zero : η = 0 := by
    have h_supp_empty : tsupport η = ∅ := by
      rw [hK_0_empty] at hη_supp_in_K_0
      exact Set.subset_empty_iff.mp hη_supp_in_K_0
    funext x
    by_contra hηx
    have hx_in_supp : x ∈ tsupport η := subset_tsupport η hηx
    rw [h_supp_empty] at hx_in_supp
    exact hx_in_supp
  have h_test_zero : standardNirenbergTest
      (d := Module.finrank ℝ E) k h η D.u_chart = 0 := by
    rw [hη_zero]
    funext x
    unfold standardNirenbergTest
    simp [DifferentialGeometry.Analysis.Sobolev.diffQuot]
  unfold chartBilinear_LHS chartBilinear_RHS
  unfold principalTerm_chartBilinear cross_1_term_chartBilinear
    cross_2_term_chartBilinear cross_3_term_chartBilinear
    c_term_chartBilinear f_term_chartBilinear
  rw [hK_0_empty]
  simp only [Measure.restrict_empty, integral_zero_measure, Finset.sum_const,
    Finset.card_univ, smul_zero, zero_add]
  have h_cthick_empty : Metric.cthickening |h| (∅ : Set EuclN) = ∅ :=
    Metric.cthickening_empty |h|
  rw [h_cthick_empty]
  simp [Measure.restrict_empty, integral_zero_measure]


omit [NeZero (Module.finrank ℝ E)] in
theorem chartBilinear_substitution_identity_holds_composite
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {K_0 : Set EuclN}
    {η : EuclN → ℝ}
    (hη_supp_in_K_0 : tsupport η ⊆ K_0)
    (k : Fin (Module.finrank ℝ E))
    {_R₀ : ℝ} {h : ℝ}
    (h_substitution_identity_holds :
      h ≠ 0 → K_0 ≠ ∅ →
      chartBilinear_LHS (I := I) (M := M) D K_0 η k h =
      chartBilinear_RHS (I := I) (M := M) D K_0 η k h) :
    chartBilinear_LHS (I := I) (M := M) D K_0 η k h =
    chartBilinear_RHS (I := I) (M := M) D K_0 η k h := by
  classical
  by_cases hh : h = 0
  · rw [hh]
    exact chartBilinear_substitution_identity_zero_h (I := I) (M := M)
      D K_0 η k
  · by_cases hK_0_empty : K_0 = ∅
    · exact chartBilinear_substitution_identity_K_0_empty (I := I) (M := M)
        D hK_0_empty η hη_supp_in_K_0 k h
    · exact h_substitution_identity_holds hh hK_0_empty

omit [NeZero (Module.finrank ℝ E)] in
theorem chartBilinear_substitution_identity_zero_h_unconditional
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    (K_0 : Set EuclN) (η : EuclN → ℝ)
    (k : Fin (Module.finrank ℝ E)) :
    chartBilinear_LHS (I := I) (M := M) D K_0 η k 0 =
    chartBilinear_RHS (I := I) (M := M) D K_0 η k 0 :=
  chartBilinear_substitution_identity_zero_h (I := I) (M := M) D K_0 η k

omit [NeZero (Module.finrank ℝ E)] in
theorem chartBilinear_substitution_identity_K_0_empty_unconditional
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {K_0 : Set EuclN} (hK_0_empty : K_0 = ∅)
    (η : EuclN → ℝ)
    (hη_supp_in_K_0 : tsupport η ⊆ K_0)
    (k : Fin (Module.finrank ℝ E)) (h : ℝ) :
    chartBilinear_LHS (I := I) (M := M) D K_0 η k h =
    chartBilinear_RHS (I := I) (M := M) D K_0 η k h :=
  chartBilinear_substitution_identity_K_0_empty (I := I) (M := M)
    D hK_0_empty η hη_supp_in_K_0 k h
omit [NeZero (Module.finrank ℝ E)] in
theorem chartBilinear_substitution_identity_with_hypothesis
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {K_0 : Set EuclN} (hK_0_compact : IsCompact K_0)
    (hK_0_in : K_0 ⊆ chartTargetEuclid (I := I) (M := M) α)
    {η : EuclN → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_supp : HasCompactSupport η)
    (hη_supp_in_K_0 : tsupport η ⊆ K_0)
    (k : Fin (Module.finrank ℝ E))
    {R₀ : ℝ} {h : ℝ} (hh : h ≠ 0) (hh_le : |h| ≤ R₀)
    (h_thick : Metric.cthickening |h| K_0 ⊆
      chartTargetEuclid (I := I) (M := M) α)
    (h_substitution_identity_holds :
      chartBilinear_LHS (I := I) (M := M) D K_0 η k h =
      chartBilinear_RHS (I := I) (M := M) D K_0 η k h) :
    chartBilinear_LHS (I := I) (M := M) D K_0 η k h =
    chartBilinear_RHS (I := I) (M := M) D K_0 η k h :=
  nirenberg_substitution_identity_chartBilinear_compact (I := I) (M := M)
    D hK_0_compact hK_0_in hη hη_supp hη_supp_in_K_0 k hh hh_le h_thick
    h_substitution_identity_holds


end SubstitutionDischargeFinal
end Sobolev
end Analysis
end DifferentialGeometry
