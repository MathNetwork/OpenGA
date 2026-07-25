import DifferentialGeometry.Geometry.Operator.Hessian
import DifferentialGeometry.Geometry.Operator.VossWeyl
import DifferentialGeometry.Analysis.Integration.Measure.Family
import DifferentialGeometry.Geometry.Operator.HessianTraceChartGramRegularity


noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold Topology ContDiff Matrix

namespace DifferentialGeometry
namespace Integral
namespace DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure

omit [NeZero (Module.finrank ℝ E)] in
lemma partialDeriv_chartInvGramOnE_eq
    (g : SmoothRiemannianMetric I M) (α : M)
    (y₀ : E) (l : Fin (Module.finrank ℝ E))
    (j p : Fin (Module.finrank ℝ E))
    (hy : y₀ ∈ interior (extChartAt I α).target) :
    partialDeriv (E := E) l (chartInvGramOnE (I := I) g α j p) y₀ =
      -∑ a : Fin (Module.finrank ℝ E),
        ∑ b : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j a y₀ *
            chartInvGramOnE (I := I) g α b p y₀ *
            partialDeriv (E := E) l (chartGramOnE (I := I) g α a b) y₀ := by
  classical
  have hytgt : y₀ ∈ (extChartAt I α).target := interior_subset hy
  set z₀ : M := (extChartAt I α).symm y₀
  have hz_base : z₀ ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    have hsource : (extChartAt I α).symm y₀ ∈ (extChartAt I α).source :=
      (extChartAt I α).map_target hytgt
    rw [extChartAt_source_eq_chartAt_source (I := I)] at hsource
    rw [trivializationAt_baseSet_eq_chartAt_source]
    exact hsource
  have hidentity : ∀ (e : Fin (Module.finrank ℝ E)) (y : E),
      y ∈ (extChartAt I α).target →
      ∑ b : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α e b y * chartInvGramOnE (I := I) g α b p y =
          if e = p then (1 : ℝ) else 0 := by
    intro e y hy_target
    have hy_base : (extChartAt I α).symm y ∈
        (trivializationAt E (TangentSpace I) α).baseSet := by
      have hsource : (extChartAt I α).symm y ∈ (extChartAt I α).source :=
        (extChartAt I α).map_target hy_target
      rw [extChartAt_source_eq_chartAt_source (I := I)] at hsource
      rw [trivializationAt_baseSet_eq_chartAt_source]
      exact hsource
    have hprod_eq :
        ∑ b : Fin (Module.finrank ℝ E),
          chartGramOnE (I := I) g α e b y * chartInvGramOnE (I := I) g α b p y =
        (chartGramMatrix (I := I) g α ((extChartAt I α).symm y) *
          chartInvGramMatrix (I := I) g α ((extChartAt I α).symm y)) e p := by
      simp only [Matrix.mul_apply]
      rfl
    rw [hprod_eq]
    rw [chartGramMatrix_mul_chartInvGramMatrix (I := I) g α hy_base]
    by_cases hep : e = p
    · subst hep
      simp
    · rw [if_neg hep]
      exact Matrix.one_apply_ne hep
  have hf_const : ∀ y ∈ interior (extChartAt I α).target,
      (∑ b : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α j b y * chartInvGramOnE (I := I) g α b p y) =
        (if j = p then (1 : ℝ) else 0) := by
    intro y hy_int
    exact hidentity j y (interior_subset hy_int)
  have hop_int : IsOpen (interior (extChartAt I α).target) := isOpen_interior
  have hy_nhd : interior (extChartAt I α).target ∈ 𝓝 y₀ := hop_int.mem_nhds hy
  have hf_diff : ∀ b : Fin (Module.finrank ℝ E),
      DifferentiableAt ℝ (fun y : E => chartGramOnE (I := I) g α j b y *
        chartInvGramOnE (I := I) g α b p y) y₀ :=
    fun b => DifferentiableAt.fun_mul
      (chartGramOnE_differentiableAt_interior (I := I) g α j b hy)
      (chartInvGramOnE_differentiableAt_interior (I := I) g α b p hy)
  have hsum_diff : DifferentiableAt ℝ (fun y : E =>
      ∑ b : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α j b y *
          chartInvGramOnE (I := I) g α b p y) y₀ := by
    refine DifferentiableAt.fun_sum ?_
    intros b _
    exact hf_diff b
  set c : ℝ := (if j = p then (1 : ℝ) else 0) with hc_def
  set fS : E → ℝ := fun y =>
    ∑ b : Fin (Module.finrank ℝ E),
      chartGramOnE (I := I) g α j b y *
        chartInvGramOnE (I := I) g α b p y with hfS_def
  have hfS_eventually : ∀ᶠ y in 𝓝 y₀, fS y = c := by
    rw [Filter.eventually_iff_exists_mem]
    refine ⟨interior (extChartAt I α).target, hy_nhd, ?_⟩
    intro y hy_int
    rw [hfS_def, hc_def]
    exact hf_const y hy_int
  have hfS_partialDeriv_zero : partialDeriv (E := E) l fS y₀ = 0 := by
    have hfderiv_eq_zero : fderiv ℝ fS y₀ = 0 := by
      have h1 : fderiv ℝ fS y₀ = fderiv ℝ (fun _ : E => c) y₀ :=
        Filter.EventuallyEq.fderiv_eq hfS_eventually
      rw [h1]
      simp
    unfold partialDeriv
    rw [hfderiv_eq_zero]
    rfl
  have hexpand : partialDeriv (E := E) l fS y₀ =
      ∑ b : Fin (Module.finrank ℝ E),
        (partialDeriv (E := E) l (chartGramOnE (I := I) g α j b) y₀ *
            chartInvGramOnE (I := I) g α b p y₀ +
          chartGramOnE (I := I) g α j b y₀ *
            partialDeriv (E := E) l (chartInvGramOnE (I := I) g α b p) y₀) := by
    rw [hfS_def]
    unfold partialDeriv
    rw [fderiv_fun_sum (fun b _ => hf_diff b)]
    rw [ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [fderiv_fun_mul (𝕜 := ℝ)
      (chartGramOnE_differentiableAt_interior (I := I) g α j b hy)
      (chartInvGramOnE_differentiableAt_interior (I := I) g α b p hy)]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  rw [hexpand] at hfS_partialDeriv_zero
  have hidentity_ap : ∀ a : Fin (Module.finrank ℝ E),
      ∑ b : Fin (Module.finrank ℝ E),
        (partialDeriv (E := E) l (chartGramOnE (I := I) g α a b) y₀ *
            chartInvGramOnE (I := I) g α b p y₀ +
          chartGramOnE (I := I) g α a b y₀ *
            partialDeriv (E := E) l (chartInvGramOnE (I := I) g α b p) y₀) = 0 := by
    intro a
    have hfS_a_eventually : ∀ᶠ y in 𝓝 y₀,
        (∑ b : Fin (Module.finrank ℝ E),
          chartGramOnE (I := I) g α a b y * chartInvGramOnE (I := I) g α b p y) =
            (if a = p then (1 : ℝ) else 0) := by
      rw [Filter.eventually_iff_exists_mem]
      refine ⟨interior (extChartAt I α).target, hy_nhd, ?_⟩
      intro y hy_int
      exact hidentity a y (interior_subset hy_int)
    have hf_diff_a : ∀ b : Fin (Module.finrank ℝ E),
        DifferentiableAt ℝ (fun y : E => chartGramOnE (I := I) g α a b y *
          chartInvGramOnE (I := I) g α b p y) y₀ :=
      fun b => DifferentiableAt.fun_mul
        (chartGramOnE_differentiableAt_interior (I := I) g α a b hy)
        (chartInvGramOnE_differentiableAt_interior (I := I) g α b p hy)
    have hf_a_diff : DifferentiableAt ℝ (fun y : E =>
        ∑ b : Fin (Module.finrank ℝ E),
          chartGramOnE (I := I) g α a b y *
            chartInvGramOnE (I := I) g α b p y) y₀ :=
      DifferentiableAt.fun_sum (fun b _ => hf_diff_a b)
    have hpartial_zero : partialDeriv (E := E) l (fun y : E =>
        ∑ b : Fin (Module.finrank ℝ E),
          chartGramOnE (I := I) g α a b y *
            chartInvGramOnE (I := I) g α b p y) y₀ = 0 := by
      have hfderiv_eq_zero : fderiv ℝ (fun y : E =>
          ∑ b : Fin (Module.finrank ℝ E),
            chartGramOnE (I := I) g α a b y *
              chartInvGramOnE (I := I) g α b p y) y₀ = 0 := by
        have h1 := Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) hfS_a_eventually
        rw [h1]
        simp
      unfold partialDeriv
      rw [hfderiv_eq_zero]
      rfl
    have hexpand_a : partialDeriv (E := E) l (fun y : E =>
        ∑ b : Fin (Module.finrank ℝ E),
          chartGramOnE (I := I) g α a b y *
            chartInvGramOnE (I := I) g α b p y) y₀ =
        ∑ b : Fin (Module.finrank ℝ E),
          (partialDeriv (E := E) l (chartGramOnE (I := I) g α a b) y₀ *
              chartInvGramOnE (I := I) g α b p y₀ +
            chartGramOnE (I := I) g α a b y₀ *
              partialDeriv (E := E) l (chartInvGramOnE (I := I) g α b p) y₀) := by
      unfold partialDeriv
      rw [fderiv_fun_sum (fun b _ => hf_diff_a b)]
      rw [ContinuousLinearMap.sum_apply]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      rw [fderiv_fun_mul (𝕜 := ℝ)
        (chartGramOnE_differentiableAt_interior (I := I) g α a b hy)
        (chartInvGramOnE_differentiableAt_interior (I := I) g α b p hy)]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
      ring
    rw [hexpand_a] at hpartial_zero
    exact hpartial_zero
  have hmul_a : ∀ a : Fin (Module.finrank ℝ E),
      chartInvGramOnE (I := I) g α j a y₀ *
        ∑ b : Fin (Module.finrank ℝ E),
          (partialDeriv (E := E) l (chartGramOnE (I := I) g α a b) y₀ *
              chartInvGramOnE (I := I) g α b p y₀ +
            chartGramOnE (I := I) g α a b y₀ *
              partialDeriv (E := E) l (chartInvGramOnE (I := I) g α b p) y₀) = 0 := by
    intro a
    rw [hidentity_ap a, mul_zero]
  have hsum_zero : ∑ a : Fin (Module.finrank ℝ E),
      chartInvGramOnE (I := I) g α j a y₀ *
        ∑ b : Fin (Module.finrank ℝ E),
          (partialDeriv (E := E) l (chartGramOnE (I := I) g α a b) y₀ *
              chartInvGramOnE (I := I) g α b p y₀ +
            chartGramOnE (I := I) g α a b y₀ *
              partialDeriv (E := E) l (chartInvGramOnE (I := I) g α b p) y₀) = 0 := by
    refine Finset.sum_eq_zero ?_
    intros a _
    exact hmul_a a
  have hsplit : ∑ a : Fin (Module.finrank ℝ E),
      chartInvGramOnE (I := I) g α j a y₀ *
        ∑ b : Fin (Module.finrank ℝ E),
          (partialDeriv (E := E) l (chartGramOnE (I := I) g α a b) y₀ *
              chartInvGramOnE (I := I) g α b p y₀ +
            chartGramOnE (I := I) g α a b y₀ *
              partialDeriv (E := E) l (chartInvGramOnE (I := I) g α b p) y₀) =
      (∑ a : Fin (Module.finrank ℝ E),
        ∑ b : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j a y₀ *
            (partialDeriv (E := E) l (chartGramOnE (I := I) g α a b) y₀ *
              chartInvGramOnE (I := I) g α b p y₀)) +
      (∑ a : Fin (Module.finrank ℝ E),
        ∑ b : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j a y₀ *
            (chartGramOnE (I := I) g α a b y₀ *
              partialDeriv (E := E) l (chartInvGramOnE (I := I) g α b p) y₀)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    ring
  rw [hsplit] at hsum_zero
  have hsecond : (∑ a : Fin (Module.finrank ℝ E),
        ∑ b : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j a y₀ *
            (chartGramOnE (I := I) g α a b y₀ *
              partialDeriv (E := E) l (chartInvGramOnE (I := I) g α b p) y₀)) =
      partialDeriv (E := E) l (chartInvGramOnE (I := I) g α j p) y₀ := by
    rw [show (∑ a : Fin (Module.finrank ℝ E),
              ∑ b : Fin (Module.finrank ℝ E),
                chartInvGramOnE (I := I) g α j a y₀ *
                  (chartGramOnE (I := I) g α a b y₀ *
                    partialDeriv (E := E) l (chartInvGramOnE (I := I) g α b p) y₀)) =
          (∑ b : Fin (Module.finrank ℝ E),
            (∑ a : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g α j a y₀ *
                chartGramOnE (I := I) g α a b y₀) *
              partialDeriv (E := E) l (chartInvGramOnE (I := I) g α b p) y₀) from by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      ring]
    have hinner : ∀ b : Fin (Module.finrank ℝ E),
        (∑ a : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j a y₀ *
            chartGramOnE (I := I) g α a b y₀) =
        (if j = b then (1 : ℝ) else 0) := by
      intro b
      have hprod_eq :
          (∑ a : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α j a y₀ *
              chartGramOnE (I := I) g α a b y₀) =
          (chartInvGramMatrix (I := I) g α z₀ *
            chartGramMatrix (I := I) g α z₀) j b := by
        simp only [Matrix.mul_apply]
        rfl
      rw [hprod_eq]
      rw [chartInvGramMatrix_mul_chartGramMatrix (I := I) g α hz_base]
      by_cases hjb : j = b
      · subst hjb
        simp
      · rw [if_neg hjb]
        exact Matrix.one_apply_ne hjb
    rw [show (∑ b : Fin (Module.finrank ℝ E),
            (∑ a : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g α j a y₀ *
                chartGramOnE (I := I) g α a b y₀) *
              partialDeriv (E := E) l (chartInvGramOnE (I := I) g α b p) y₀) =
        ∑ b : Fin (Module.finrank ℝ E),
          (if j = b then (1 : ℝ) else 0) *
            partialDeriv (E := E) l (chartInvGramOnE (I := I) g α b p) y₀ from by
      refine Finset.sum_congr rfl (fun b _ => ?_)
      rw [hinner b]]
    rw [Finset.sum_eq_single j]
    · rw [if_pos rfl]; ring
    · intros b _ hbj
      have hjb : ¬ j = b := fun h => hbj h.symm
      rw [if_neg hjb, zero_mul]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  rw [hsecond] at hsum_zero
  have hgoal : partialDeriv (E := E) l (chartInvGramOnE (I := I) g α j p) y₀ =
      -(∑ a : Fin (Module.finrank ℝ E),
        ∑ b : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j a y₀ *
            (partialDeriv (E := E) l (chartGramOnE (I := I) g α a b) y₀ *
              chartInvGramOnE (I := I) g α b p y₀)) := by
    linarith [hsum_zero]
  rw [hgoal]
  congr 1
  refine Finset.sum_congr rfl (fun a _ => ?_)
  refine Finset.sum_congr rfl (fun b _ => ?_)
  ring

omit [NeZero (Module.finrank ℝ E)] in
lemma partialDeriv2_chartInvGramOnE_eq
    (g : SmoothRiemannianMetric I M) (α : M)
    (y₀ : E) (i j : Fin (Module.finrank ℝ E))
    (k l : Fin (Module.finrank ℝ E))
    (hy : y₀ ∈ interior (extChartAt I α).target) :
    partialDeriv (E := E) i
        (fun y' : E => partialDeriv (E := E) j
          (chartInvGramOnE (I := I) g α k l) y') y₀ =
      (∑ p : Fin (Module.finrank ℝ E),
        ∑ q : Fin (Module.finrank ℝ E),
        ∑ r : Fin (Module.finrank ℝ E),
        ∑ s : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α k r y₀ *
            chartInvGramOnE (I := I) g α p s y₀ *
            chartInvGramOnE (I := I) g α q l y₀ *
            partialDeriv (E := E) i (chartGramOnE (I := I) g α r s) y₀ *
            partialDeriv (E := E) j (chartGramOnE (I := I) g α p q) y₀) +
      (∑ p : Fin (Module.finrank ℝ E),
        ∑ q : Fin (Module.finrank ℝ E),
        ∑ r : Fin (Module.finrank ℝ E),
        ∑ s : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α k p y₀ *
            chartInvGramOnE (I := I) g α q r y₀ *
            chartInvGramOnE (I := I) g α l s y₀ *
            partialDeriv (E := E) i (chartGramOnE (I := I) g α r s) y₀ *
            partialDeriv (E := E) j (chartGramOnE (I := I) g α p q) y₀) -
      (∑ p : Fin (Module.finrank ℝ E),
        ∑ q : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α k p y₀ *
            chartInvGramOnE (I := I) g α q l y₀ *
            partialDeriv (E := E) i
              (fun y' : E => partialDeriv (E := E) j
                (chartGramOnE (I := I) g α p q) y') y₀) := by
  classical
  have hop_int : IsOpen (interior (extChartAt I α).target) := isOpen_interior
  have hy_nhd : interior (extChartAt I α).target ∈ 𝓝 y₀ := hop_int.mem_nhds hy
  set F : E → ℝ := fun y' =>
    -∑ p : Fin (Module.finrank ℝ E),
      ∑ q : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g α k p y' *
          chartInvGramOnE (I := I) g α q l y' *
          partialDeriv (E := E) j (chartGramOnE (I := I) g α p q) y' with hF_def
  have hLHS_F : ∀ᶠ y' in 𝓝 y₀,
      partialDeriv (E := E) j (chartInvGramOnE (I := I) g α k l) y' = F y' := by
    rw [Filter.eventually_iff_exists_mem]
    refine ⟨interior (extChartAt I α).target, hy_nhd, ?_⟩
    intro y' hy'_int
    rw [hF_def]
    exact partialDeriv_chartInvGramOnE_eq (I := I) g α y' j k l hy'_int
  have hfderiv_eq : fderiv ℝ
      (fun y' : E => partialDeriv (E := E) j
        (chartInvGramOnE (I := I) g α k l) y') y₀ =
      fderiv ℝ F y₀ :=
    Filter.EventuallyEq.fderiv_eq hLHS_F
  have hpartial_eq : partialDeriv (E := E) i
      (fun y' : E => partialDeriv (E := E) j
        (chartInvGramOnE (I := I) g α k l) y') y₀ =
      partialDeriv (E := E) i F y₀ := by
    change (fderiv ℝ (fun y' : E => partialDeriv (E := E) j
        (chartInvGramOnE (I := I) g α k l) y') y₀)
        ((chartModelBasis E) i) =
      (fderiv ℝ F y₀) ((chartModelBasis E) i)
    rw [hfderiv_eq]
  rw [hpartial_eq]
  have hG_diff_kp : ∀ p : Fin (Module.finrank ℝ E),
      DifferentiableAt ℝ (chartInvGramOnE (I := I) g α k p) y₀ :=
    fun p => chartInvGramOnE_differentiableAt_interior (I := I) g α k p hy
  have hG_diff_ql : ∀ q : Fin (Module.finrank ℝ E),
      DifferentiableAt ℝ (chartInvGramOnE (I := I) g α q l) y₀ :=
    fun q => chartInvGramOnE_differentiableAt_interior (I := I) g α q l hy
  have h_dG_diff : ∀ p q : Fin (Module.finrank ℝ E),
      DifferentiableAt ℝ
        (partialDeriv (E := E) j (chartGramOnE (I := I) g α p q)) y₀ :=
    fun p q => partialDeriv_chartGramOnE_differentiableAt_interior
      (I := I) g α j p q hy
  have h_summand_diff : ∀ p q : Fin (Module.finrank ℝ E),
      DifferentiableAt ℝ
        (fun y' : E => chartInvGramOnE (I := I) g α k p y' *
          chartInvGramOnE (I := I) g α q l y' *
          partialDeriv (E := E) j (chartGramOnE (I := I) g α p q) y') y₀ :=
    fun p q => DifferentiableAt.fun_mul
      (DifferentiableAt.fun_mul (hG_diff_kp p) (hG_diff_ql q))
      (h_dG_diff p q)
  have h_inner_sum_diff : ∀ p : Fin (Module.finrank ℝ E),
      DifferentiableAt ℝ
        (fun y' : E => ∑ q : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α k p y' *
          chartInvGramOnE (I := I) g α q l y' *
          partialDeriv (E := E) j (chartGramOnE (I := I) g α p q) y') y₀ :=
    fun p => DifferentiableAt.fun_sum (fun q _ => h_summand_diff p q)
  have hpartial_F : partialDeriv (E := E) i F y₀ =
      -∑ p : Fin (Module.finrank ℝ E),
        ∑ q : Fin (Module.finrank ℝ E),
          (partialDeriv (E := E) i (chartInvGramOnE (I := I) g α k p) y₀ *
              chartInvGramOnE (I := I) g α q l y₀ *
              partialDeriv (E := E) j (chartGramOnE (I := I) g α p q) y₀ +
            chartInvGramOnE (I := I) g α k p y₀ *
              partialDeriv (E := E) i (chartInvGramOnE (I := I) g α q l) y₀ *
              partialDeriv (E := E) j (chartGramOnE (I := I) g α p q) y₀ +
            chartInvGramOnE (I := I) g α k p y₀ *
              chartInvGramOnE (I := I) g α q l y₀ *
              partialDeriv (E := E) i
                (fun y' : E => partialDeriv (E := E) j
                  (chartGramOnE (I := I) g α p q) y') y₀) := by
    change (fderiv ℝ F y₀) ((chartModelBasis E) i) = _
    rw [hF_def]
    rw [show
      fderiv ℝ (fun y' : E =>
          -∑ p : Fin (Module.finrank ℝ E),
            ∑ q : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g α k p y' *
                chartInvGramOnE (I := I) g α q l y' *
                partialDeriv (E := E) j (chartGramOnE (I := I) g α p q) y') y₀ =
        -fderiv ℝ (fun y' : E =>
          ∑ p : Fin (Module.finrank ℝ E),
            ∑ q : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g α k p y' *
                chartInvGramOnE (I := I) g α q l y' *
                partialDeriv (E := E) j (chartGramOnE (I := I) g α p q) y') y₀ from
      fderiv_neg]
    rw [fderiv_fun_sum (fun p _ => h_inner_sum_diff p)]
    simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.sum_apply, neg_inj]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [fderiv_fun_sum (fun q _ => h_summand_diff p q)]
    rw [ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [fderiv_fun_mul (𝕜 := ℝ)
      (DifferentiableAt.fun_mul (hG_diff_kp p) (hG_diff_ql q))
      (h_dG_diff p q)]
    rw [fderiv_fun_mul (𝕜 := ℝ) (hG_diff_kp p) (hG_diff_ql q)]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul]
    change chartInvGramOnE (I := I) g α k p y₀ *
        chartInvGramOnE (I := I) g α q l y₀ *
        partialDeriv (E := E) i
          (fun y' : E => partialDeriv (E := E) j
            (chartGramOnE (I := I) g α p q) y') y₀ +
      partialDeriv (E := E) j (chartGramOnE (I := I) g α p q) y₀ *
        (chartInvGramOnE (I := I) g α k p y₀ *
          partialDeriv (E := E) i (chartInvGramOnE (I := I) g α q l) y₀ +
        chartInvGramOnE (I := I) g α q l y₀ *
          partialDeriv (E := E) i (chartInvGramOnE (I := I) g α k p) y₀) =
      partialDeriv (E := E) i (chartInvGramOnE (I := I) g α k p) y₀ *
        chartInvGramOnE (I := I) g α q l y₀ *
        partialDeriv (E := E) j (chartGramOnE (I := I) g α p q) y₀ +
      chartInvGramOnE (I := I) g α k p y₀ *
        partialDeriv (E := E) i (chartInvGramOnE (I := I) g α q l) y₀ *
        partialDeriv (E := E) j (chartGramOnE (I := I) g α p q) y₀ +
      chartInvGramOnE (I := I) g α k p y₀ *
        chartInvGramOnE (I := I) g α q l y₀ *
        partialDeriv (E := E) i
          (fun y' : E => partialDeriv (E := E) j
            (chartGramOnE (I := I) g α p q) y') y₀
    ring
  rw [hpartial_F]
  have hpoint_kp : ∀ p : Fin (Module.finrank ℝ E),
      partialDeriv (E := E) i (chartInvGramOnE (I := I) g α k p) y₀ =
        -∑ r : Fin (Module.finrank ℝ E),
          ∑ s : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α k r y₀ *
              chartInvGramOnE (I := I) g α s p y₀ *
              partialDeriv (E := E) i (chartGramOnE (I := I) g α r s) y₀ :=
    fun p => partialDeriv_chartInvGramOnE_eq (I := I) g α y₀ i k p hy
  have hpoint_ql : ∀ q : Fin (Module.finrank ℝ E),
      partialDeriv (E := E) i (chartInvGramOnE (I := I) g α q l) y₀ =
        -∑ r : Fin (Module.finrank ℝ E),
          ∑ s : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α q r y₀ *
              chartInvGramOnE (I := I) g α s l y₀ *
              partialDeriv (E := E) i (chartGramOnE (I := I) g α r s) y₀ :=
    fun q => partialDeriv_chartInvGramOnE_eq (I := I) g α y₀ i q l hy
  have hsymm : ∀ a b : Fin (Module.finrank ℝ E),
      chartInvGramOnE (I := I) g α a b y₀ =
        chartInvGramOnE (I := I) g α b a y₀ := by
    intro a b
    unfold chartInvGramOnE
    set z := (extChartAt I α).symm y₀
    have hG_hermit : (chartGramMatrix (I := I) g α z).IsHermitian :=
      chartGramMatrix_isHermitian (I := I) g α z
    have hGinv_hermit : (chartGramMatrix (I := I) g α z)⁻¹.IsHermitian :=
      hG_hermit.inv
    have hentry := hGinv_hermit.apply a b
    unfold chartInvGramMatrix
    have hstar : star ((chartGramMatrix (I := I) g α z)⁻¹ b a) =
        (chartGramMatrix (I := I) g α z)⁻¹ a b := hentry
    rw [show star ((chartGramMatrix (I := I) g α z)⁻¹ b a) =
        (chartGramMatrix (I := I) g α z)⁻¹ b a from rfl] at hstar
    exact hstar.symm
  refine (?_ : _ = _)
  have hpq : ∀ p q : Fin (Module.finrank ℝ E),
      partialDeriv (E := E) i (chartInvGramOnE (I := I) g α k p) y₀ *
          chartInvGramOnE (I := I) g α q l y₀ *
          partialDeriv (E := E) j (chartGramOnE (I := I) g α p q) y₀ +
        chartInvGramOnE (I := I) g α k p y₀ *
          partialDeriv (E := E) i (chartInvGramOnE (I := I) g α q l) y₀ *
          partialDeriv (E := E) j (chartGramOnE (I := I) g α p q) y₀ +
        chartInvGramOnE (I := I) g α k p y₀ *
          chartInvGramOnE (I := I) g α q l y₀ *
          partialDeriv (E := E) i
            (fun y' : E => partialDeriv (E := E) j
              (chartGramOnE (I := I) g α p q) y') y₀ =
      (∑ r : Fin (Module.finrank ℝ E),
        ∑ s : Fin (Module.finrank ℝ E),
          -(chartInvGramOnE (I := I) g α k r y₀ *
            chartInvGramOnE (I := I) g α s p y₀ *
            chartInvGramOnE (I := I) g α q l y₀ *
            partialDeriv (E := E) i (chartGramOnE (I := I) g α r s) y₀ *
            partialDeriv (E := E) j (chartGramOnE (I := I) g α p q) y₀)) +
      (∑ r : Fin (Module.finrank ℝ E),
        ∑ s : Fin (Module.finrank ℝ E),
          -(chartInvGramOnE (I := I) g α k p y₀ *
            chartInvGramOnE (I := I) g α q r y₀ *
            chartInvGramOnE (I := I) g α s l y₀ *
            partialDeriv (E := E) i (chartGramOnE (I := I) g α r s) y₀ *
            partialDeriv (E := E) j (chartGramOnE (I := I) g α p q) y₀)) +
      chartInvGramOnE (I := I) g α k p y₀ *
        chartInvGramOnE (I := I) g α q l y₀ *
        partialDeriv (E := E) i
          (fun y' : E => partialDeriv (E := E) j
            (chartGramOnE (I := I) g α p q) y') y₀ := by
    intro p q
    rw [hpoint_kp p, hpoint_ql q]
    have h1 : (-∑ r : Fin (Module.finrank ℝ E),
        ∑ s : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α k r y₀ *
            chartInvGramOnE (I := I) g α s p y₀ *
            partialDeriv (E := E) i (chartGramOnE (I := I) g α r s) y₀) *
        chartInvGramOnE (I := I) g α q l y₀ *
        partialDeriv (E := E) j (chartGramOnE (I := I) g α p q) y₀ =
      ∑ r : Fin (Module.finrank ℝ E),
        ∑ s : Fin (Module.finrank ℝ E),
          -(chartInvGramOnE (I := I) g α k r y₀ *
            chartInvGramOnE (I := I) g α s p y₀ *
            chartInvGramOnE (I := I) g α q l y₀ *
            partialDeriv (E := E) i (chartGramOnE (I := I) g α r s) y₀ *
            partialDeriv (E := E) j (chartGramOnE (I := I) g α p q) y₀) := by
      rw [neg_mul, neg_mul, Finset.sum_mul, Finset.sum_mul]
      rw [show
        -∑ r : Fin (Module.finrank ℝ E),
          (∑ s : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α k r y₀ *
              chartInvGramOnE (I := I) g α s p y₀ *
              partialDeriv (E := E) i (chartGramOnE (I := I) g α r s) y₀) *
            chartInvGramOnE (I := I) g α q l y₀ *
            partialDeriv (E := E) j (chartGramOnE (I := I) g α p q) y₀ =
        ∑ r : Fin (Module.finrank ℝ E),
          -((∑ s : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α k r y₀ *
              chartInvGramOnE (I := I) g α s p y₀ *
              partialDeriv (E := E) i (chartGramOnE (I := I) g α r s) y₀) *
            chartInvGramOnE (I := I) g α q l y₀ *
            partialDeriv (E := E) j (chartGramOnE (I := I) g α p q) y₀) by
        rw [Finset.sum_neg_distrib]]
      refine Finset.sum_congr rfl (fun r _ => ?_)
      rw [Finset.sum_mul, Finset.sum_mul]
      rw [show
        -∑ s : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α k r y₀ *
            chartInvGramOnE (I := I) g α s p y₀ *
            partialDeriv (E := E) i (chartGramOnE (I := I) g α r s) y₀ *
            chartInvGramOnE (I := I) g α q l y₀ *
            partialDeriv (E := E) j (chartGramOnE (I := I) g α p q) y₀ =
        ∑ s : Fin (Module.finrank ℝ E),
          -(chartInvGramOnE (I := I) g α k r y₀ *
            chartInvGramOnE (I := I) g α s p y₀ *
            partialDeriv (E := E) i (chartGramOnE (I := I) g α r s) y₀ *
            chartInvGramOnE (I := I) g α q l y₀ *
            partialDeriv (E := E) j (chartGramOnE (I := I) g α p q) y₀) by
        rw [Finset.sum_neg_distrib]]
      refine Finset.sum_congr rfl (fun s _ => ?_)
      ring
    have h2 : chartInvGramOnE (I := I) g α k p y₀ *
        (-∑ r : Fin (Module.finrank ℝ E),
          ∑ s : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α q r y₀ *
              chartInvGramOnE (I := I) g α s l y₀ *
              partialDeriv (E := E) i (chartGramOnE (I := I) g α r s) y₀) *
        partialDeriv (E := E) j (chartGramOnE (I := I) g α p q) y₀ =
      ∑ r : Fin (Module.finrank ℝ E),
        ∑ s : Fin (Module.finrank ℝ E),
          -(chartInvGramOnE (I := I) g α k p y₀ *
            chartInvGramOnE (I := I) g α q r y₀ *
            chartInvGramOnE (I := I) g α s l y₀ *
            partialDeriv (E := E) i (chartGramOnE (I := I) g α r s) y₀ *
            partialDeriv (E := E) j (chartGramOnE (I := I) g α p q) y₀) := by
      rw [mul_neg, neg_mul, Finset.mul_sum, Finset.sum_mul]
      rw [show
        -∑ r : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α k p y₀ *
            (∑ s : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g α q r y₀ *
                chartInvGramOnE (I := I) g α s l y₀ *
                partialDeriv (E := E) i (chartGramOnE (I := I) g α r s) y₀) *
            partialDeriv (E := E) j (chartGramOnE (I := I) g α p q) y₀ =
        ∑ r : Fin (Module.finrank ℝ E),
          -(chartInvGramOnE (I := I) g α k p y₀ *
            (∑ s : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g α q r y₀ *
                chartInvGramOnE (I := I) g α s l y₀ *
                partialDeriv (E := E) i (chartGramOnE (I := I) g α r s) y₀) *
            partialDeriv (E := E) j (chartGramOnE (I := I) g α p q) y₀) by
        rw [Finset.sum_neg_distrib]]
      refine Finset.sum_congr rfl (fun r _ => ?_)
      rw [Finset.mul_sum, Finset.sum_mul]
      rw [show
        -∑ s : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α k p y₀ *
            (chartInvGramOnE (I := I) g α q r y₀ *
              chartInvGramOnE (I := I) g α s l y₀ *
              partialDeriv (E := E) i (chartGramOnE (I := I) g α r s) y₀) *
            partialDeriv (E := E) j (chartGramOnE (I := I) g α p q) y₀ =
        ∑ s : Fin (Module.finrank ℝ E),
          -(chartInvGramOnE (I := I) g α k p y₀ *
            (chartInvGramOnE (I := I) g α q r y₀ *
              chartInvGramOnE (I := I) g α s l y₀ *
              partialDeriv (E := E) i (chartGramOnE (I := I) g α r s) y₀) *
            partialDeriv (E := E) j (chartGramOnE (I := I) g α p q) y₀) by
        rw [Finset.sum_neg_distrib]]
      refine Finset.sum_congr rfl (fun s _ => ?_)
      ring
    rw [h1, h2]
  rw [show
    (-∑ p : Fin (Module.finrank ℝ E),
      ∑ q : Fin (Module.finrank ℝ E),
        (partialDeriv (E := E) i (chartInvGramOnE (I := I) g α k p) y₀ *
            chartInvGramOnE (I := I) g α q l y₀ *
            partialDeriv (E := E) j (chartGramOnE (I := I) g α p q) y₀ +
          chartInvGramOnE (I := I) g α k p y₀ *
            partialDeriv (E := E) i (chartInvGramOnE (I := I) g α q l) y₀ *
            partialDeriv (E := E) j (chartGramOnE (I := I) g α p q) y₀ +
          chartInvGramOnE (I := I) g α k p y₀ *
            chartInvGramOnE (I := I) g α q l y₀ *
            partialDeriv (E := E) i
              (fun y' : E => partialDeriv (E := E) j
                (chartGramOnE (I := I) g α p q) y') y₀)) =
    (-∑ p : Fin (Module.finrank ℝ E),
      ∑ q : Fin (Module.finrank ℝ E),
        ((∑ r : Fin (Module.finrank ℝ E),
          ∑ s : Fin (Module.finrank ℝ E),
            -(chartInvGramOnE (I := I) g α k r y₀ *
              chartInvGramOnE (I := I) g α s p y₀ *
              chartInvGramOnE (I := I) g α q l y₀ *
              partialDeriv (E := E) i (chartGramOnE (I := I) g α r s) y₀ *
              partialDeriv (E := E) j (chartGramOnE (I := I) g α p q) y₀)) +
        (∑ r : Fin (Module.finrank ℝ E),
          ∑ s : Fin (Module.finrank ℝ E),
            -(chartInvGramOnE (I := I) g α k p y₀ *
              chartInvGramOnE (I := I) g α q r y₀ *
              chartInvGramOnE (I := I) g α s l y₀ *
              partialDeriv (E := E) i (chartGramOnE (I := I) g α r s) y₀ *
              partialDeriv (E := E) j (chartGramOnE (I := I) g α p q) y₀)) +
        chartInvGramOnE (I := I) g α k p y₀ *
          chartInvGramOnE (I := I) g α q l y₀ *
          partialDeriv (E := E) i
            (fun y' : E => partialDeriv (E := E) j
              (chartGramOnE (I := I) g α p q) y') y₀)) from by
    refine congrArg Neg.neg ?_
    refine Finset.sum_congr rfl (fun p _ => ?_)
    refine Finset.sum_congr rfl (fun q _ => ?_)
    exact hpq p q]
  simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib, neg_add_rev, neg_neg]
  rw [show
    (∑ p : Fin (Module.finrank ℝ E),
      ∑ q : Fin (Module.finrank ℝ E),
      ∑ r : Fin (Module.finrank ℝ E),
      ∑ s : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g α k r y₀ *
          chartInvGramOnE (I := I) g α p s y₀ *
          chartInvGramOnE (I := I) g α q l y₀ *
          partialDeriv (E := E) i (chartGramOnE (I := I) g α r s) y₀ *
          partialDeriv (E := E) j (chartGramOnE (I := I) g α p q) y₀) =
    (∑ p : Fin (Module.finrank ℝ E),
      ∑ q : Fin (Module.finrank ℝ E),
      ∑ r : Fin (Module.finrank ℝ E),
      ∑ s : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g α k r y₀ *
          chartInvGramOnE (I := I) g α s p y₀ *
          chartInvGramOnE (I := I) g α q l y₀ *
          partialDeriv (E := E) i (chartGramOnE (I := I) g α r s) y₀ *
          partialDeriv (E := E) j (chartGramOnE (I := I) g α p q) y₀) from by
    refine Finset.sum_congr rfl (fun p _ => ?_)
    refine Finset.sum_congr rfl (fun q _ => ?_)
    refine Finset.sum_congr rfl (fun r _ => ?_)
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [hsymm p s]]
  rw [show
    (∑ p : Fin (Module.finrank ℝ E),
      ∑ q : Fin (Module.finrank ℝ E),
      ∑ r : Fin (Module.finrank ℝ E),
      ∑ s : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g α k p y₀ *
          chartInvGramOnE (I := I) g α q r y₀ *
          chartInvGramOnE (I := I) g α l s y₀ *
          partialDeriv (E := E) i (chartGramOnE (I := I) g α r s) y₀ *
          partialDeriv (E := E) j (chartGramOnE (I := I) g α p q) y₀) =
    (∑ p : Fin (Module.finrank ℝ E),
      ∑ q : Fin (Module.finrank ℝ E),
      ∑ r : Fin (Module.finrank ℝ E),
      ∑ s : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g α k p y₀ *
          chartInvGramOnE (I := I) g α q r y₀ *
          chartInvGramOnE (I := I) g α s l y₀ *
          partialDeriv (E := E) i (chartGramOnE (I := I) g α r s) y₀ *
          partialDeriv (E := E) j (chartGramOnE (I := I) g α p q) y₀) from by
    refine Finset.sum_congr rfl (fun p _ => ?_)
    refine Finset.sum_congr rfl (fun q _ => ?_)
    refine Finset.sum_congr rfl (fun r _ => ?_)
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [hsymm l s]]
  ring

omit [NeZero (Module.finrank ℝ E)] in
lemma chartGramOnE_symm_fun
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) :
    chartGramOnE (I := I) g α i j = chartGramOnE (I := I) g α j i := by
  funext y
  exact chartGramOnE_symm (I := I) g α i j y

omit [NeZero (Module.finrank ℝ E)] in
lemma chartInvGramOnE_symm_pointwise
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) (y : E) :
    chartInvGramOnE (I := I) g α i j y = chartInvGramOnE (I := I) g α j i y := by
  unfold chartInvGramOnE
  set z := (extChartAt I α).symm y
  have hG_hermit : (chartGramMatrix (I := I) g α z).IsHermitian :=
    chartGramMatrix_isHermitian (I := I) g α z
  have hGinv_hermit : (chartGramMatrix (I := I) g α z)⁻¹.IsHermitian :=
    hG_hermit.inv
  have hentry := hGinv_hermit.apply i j
  unfold chartInvGramMatrix
  have hstar : star ((chartGramMatrix (I := I) g α z)⁻¹ j i) =
      (chartGramMatrix (I := I) g α z)⁻¹ i j := hentry
  rw [show star ((chartGramMatrix (I := I) g α z)⁻¹ j i) =
      (chartGramMatrix (I := I) g α z)⁻¹ j i from rfl] at hstar
  exact hstar.symm

end DivergenceTheorem
end Integral
end DifferentialGeometry
