import DifferentialGeometry.Analysis.Parabolic.DeTurckLinearization.LinearizedVectorField


noncomputable section

open Set Function
open scoped Topology ContDiff Matrix Manifold

namespace DifferentialGeometry
namespace PDE
namespace DeTurck
namespace DeTurckLinearization

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.DeTurck.RicciLinearization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

section Differentiability

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma chartGramOnE_differentiableAt_interior
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    DifferentiableAt ℝ (chartGramOnE (I := I) g α i j) y := by
  have hcd : ContDiffOn ℝ ∞ (chartGramOnE (I := I) g α i j)
      (extChartAt I α).target := chartGramOnE_contDiffOn (I := I) g α i j
  have hcd_int : ContDiffOn ℝ ∞ (chartGramOnE (I := I) g α i j)
      (interior (extChartAt I α).target) := hcd.mono interior_subset
  have hat : ContDiffAt ℝ ∞ (chartGramOnE (I := I) g α i j) y :=
    hcd_int.contDiffAt (isOpen_interior.mem_nhds hy)
  exact hat.differentiableAt (by simp)

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma chartInvGramOnE_differentiableAt_interior
    (g : SmoothRiemannianMetric I M) (α : M)
    (a b : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    DifferentiableAt ℝ (chartInvGramOnE (I := I) g α a b) y := by
  have hcd : ContDiffOn ℝ ∞ (chartInvGramOnE (I := I) g α a b)
      (extChartAt I α).target := chartInvGramOnE_contDiffOn (I := I) g α a b
  have hcd_int : ContDiffOn ℝ ∞ (chartInvGramOnE (I := I) g α a b)
      (interior (extChartAt I α).target) := hcd.mono interior_subset
  have hat : ContDiffAt ℝ ∞ (chartInvGramOnE (I := I) g α a b) y :=
    hcd_int.contDiffAt (isOpen_interior.mem_nhds hy)
  exact hat.differentiableAt (by simp)

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma chartLinearizedDeTurckVFPrincipal_differentiableAt
    (g g' : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (k : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    DifferentiableAt ℝ
      (fun y' => chartLinearizedDeTurckVFPrincipal (I := I) g g' α h k y') y := by
  have hcd : ContDiffOn ℝ ∞
      (fun y' => chartLinearizedDeTurckVFPrincipal (I := I) g g' α h k y')
      (interior (extChartAt I α).target) :=
    chartLinearizedDeTurckVFPrincipal_contDiffOn_interior (I := I) g g' α h k
  have hat : ContDiffAt ℝ ∞
      (fun y' => chartLinearizedDeTurckVFPrincipal (I := I) g g' α h k y') y :=
    hcd.contDiffAt (isOpen_interior.mem_nhds hy)
  exact hat.differentiableAt (by simp)

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma chartLinearizedChristoffelPrincipal_differentiableAt
    (g : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (a b k : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    DifferentiableAt ℝ
      (fun y' => chartLinearizedChristoffelPrincipal (I := I) g α h a b k y') y := by
  have hcd : ContDiffOn ℝ ∞
      (fun y' => chartLinearizedChristoffelPrincipal (I := I) g α h a b k y')
      (interior (extChartAt I α).target) :=
    (chartLinearizedChristoffelPrincipal_contDiffOn (I := I) g α h a b k).mono
      interior_subset
  have hat : ContDiffAt ℝ ∞
      (fun y' => chartLinearizedChristoffelPrincipal (I := I) g α h a b k y') y :=
    hcd.contDiffAt (isOpen_interior.mem_nhds hy)
  exact hat.differentiableAt (by simp)

end Differentiability

def chartDeTurckCorrSecondOrderPart (g g' : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (i j : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  (∑ k : Fin (Module.finrank ℝ E),
      chartGramOnE (I := I) g α k j y *
        partialDeriv (E := E) i
          (fun y' => chartLinearizedDeTurckVFPrincipal (I := I) g g' α h k y') y) +
  (∑ k : Fin (Module.finrank ℝ E),
      chartGramOnE (I := I) g α i k y *
        partialDeriv (E := E) j
          (fun y' => chartLinearizedDeTurckVFPrincipal (I := I) g g' α h k y') y)

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
@[simp] lemma chartDeTurckCorrSecondOrderPart_def
    (g g' : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (i j : Fin (Module.finrank ℝ E)) (y : E) :
    chartDeTurckCorrSecondOrderPart (I := I) g g' α h i j y =
      (∑ k : Fin (Module.finrank ℝ E),
          chartGramOnE (I := I) g α k j y *
            partialDeriv (E := E) i
              (fun y' => chartLinearizedDeTurckVFPrincipal (I := I) g g' α h k y') y) +
      (∑ k : Fin (Module.finrank ℝ E),
          chartGramOnE (I := I) g α i k y *
            partialDeriv (E := E) j
              (fun y' => chartLinearizedDeTurckVFPrincipal (I := I) g g' α h k y') y) :=
  rfl

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma partialDeriv_chartLinearizedDeTurckVFPrincipal
    (g g' : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (k d : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    partialDeriv (E := E) d
        (fun y' => chartLinearizedDeTurckVFPrincipal (I := I) g g' α h k y') y =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        (partialDeriv (E := E) d (chartInvGramOnE (I := I) g α a b) y *
            chartLinearizedChristoffelPrincipal (I := I) g α h a b k y +
          chartInvGramOnE (I := I) g α a b y *
            partialDeriv (E := E) d
              (fun y' => chartLinearizedChristoffelPrincipal (I := I) g α h a b k y')
              y) := by
  classical
  set Γ : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → E → ℝ :=
    fun a b y' => chartLinearizedChristoffelPrincipal (I := I) g α h a b k y' with hΓ
  have hΓ_diff : ∀ a b : Fin (Module.finrank ℝ E), DifferentiableAt ℝ (Γ a b) y :=
    fun a b => chartLinearizedChristoffelPrincipal_differentiableAt (I := I) g α h a b k hy
  have hG_diff : ∀ a b : Fin (Module.finrank ℝ E),
      DifferentiableAt ℝ (chartInvGramOnE (I := I) g α a b) y :=
    fun a b => chartInvGramOnE_differentiableAt_interior (I := I) g α a b hy
  have hsummand_diff : ∀ a b : Fin (Module.finrank ℝ E),
      DifferentiableAt ℝ
        (fun y' => chartInvGramOnE (I := I) g α a b y' * Γ a b y') y :=
    fun a b => (hG_diff a b).mul (hΓ_diff a b)
  have hrewrite :
      (fun y' => chartLinearizedDeTurckVFPrincipal (I := I) g g' α h k y') =
        fun y' => ∑ a : Fin (Module.finrank ℝ E),
          ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α a b y' * Γ a b y' := by
    funext y'
    rw [chartLinearizedDeTurckVFPrincipal_def]
  rw [hrewrite]
  rw [partialDeriv_sum Finset.univ
        (fun a y' => ∑ b : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α a b y' * Γ a b y')
        (fun a _ => DifferentiableAt.fun_sum (fun b _ => hsummand_diff a b))]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [partialDeriv_sum Finset.univ
        (fun b y' => chartInvGramOnE (I := I) g α a b y' * Γ a b y')
        (fun b _ => hsummand_diff a b)]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [partialDeriv_mul (chartInvGramOnE (I := I) g α a b) (Γ a b)
        (hG_diff a b) (hΓ_diff a b)]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
@[simp] theorem chartDeTurckCorrSecondOrderPart_zero
    (g g' : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) (y : E) :
    chartDeTurckCorrSecondOrderPart (I := I) g g' α
      (0 : ChartMetricPerturbation E) i j y = 0 := by
  classical
  rw [chartDeTurckCorrSecondOrderPart_def]
  have hpd : ∀ (d k : Fin (Module.finrank ℝ E)),
      partialDeriv (E := E) d
        (fun y' => chartLinearizedDeTurckVFPrincipal (I := I) g g' α
          (0 : ChartMetricPerturbation E) k y') y = 0 := by
    intro d k
    have heq : (fun y' => chartLinearizedDeTurckVFPrincipal (I := I) g g' α
        (0 : ChartMetricPerturbation E) k y') = fun _ : E => (0 : ℝ) := by
      funext y'; rw [chartLinearizedDeTurckVFPrincipal_zero]
    rw [heq, partialDeriv_const]
  have hsum1 : (∑ k : Fin (Module.finrank ℝ E),
      chartGramOnE (I := I) g α k j y *
        partialDeriv (E := E) i
          (fun y' => chartLinearizedDeTurckVFPrincipal (I := I) g g' α
            (0 : ChartMetricPerturbation E) k y') y) = 0 := by
    refine Finset.sum_eq_zero (fun k _ => ?_)
    rw [hpd i k, mul_zero]
  have hsum2 : (∑ k : Fin (Module.finrank ℝ E),
      chartGramOnE (I := I) g α i k y *
        partialDeriv (E := E) j
          (fun y' => chartLinearizedDeTurckVFPrincipal (I := I) g g' α
            (0 : ChartMetricPerturbation E) k y') y) = 0 := by
    refine Finset.sum_eq_zero (fun k _ => ?_)
    rw [hpd j k, mul_zero]
  rw [hsum1, hsum2, add_zero]

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem chartDeTurckCorrSecondOrderPart_add
    (g g' : SmoothRiemannianMetric I M) (α : M)
    (h₁ h₂ : ChartMetricPerturbation E) (i j : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    chartDeTurckCorrSecondOrderPart (I := I) g g' α (h₁ + h₂) i j y =
      chartDeTurckCorrSecondOrderPart (I := I) g g' α h₁ i j y +
        chartDeTurckCorrSecondOrderPart (I := I) g g' α h₂ i j y := by
  classical
  rw [chartDeTurckCorrSecondOrderPart_def, chartDeTurckCorrSecondOrderPart_def,
    chartDeTurckCorrSecondOrderPart_def]
  have hadd : ∀ (d k : Fin (Module.finrank ℝ E)),
      partialDeriv (E := E) d
          (fun y' => chartLinearizedDeTurckVFPrincipal (I := I) g g' α (h₁ + h₂) k y')
          y =
        partialDeriv (E := E) d
            (fun y' => chartLinearizedDeTurckVFPrincipal (I := I) g g' α h₁ k y') y +
          partialDeriv (E := E) d
            (fun y' => chartLinearizedDeTurckVFPrincipal (I := I) g g' α h₂ k y') y := by
    intro d k
    have heq : (fun y' => chartLinearizedDeTurckVFPrincipal (I := I) g g' α
          (h₁ + h₂) k y') =
        fun y' => chartLinearizedDeTurckVFPrincipal (I := I) g g' α h₁ k y' +
          chartLinearizedDeTurckVFPrincipal (I := I) g g' α h₂ k y' := by
      funext y'; rw [chartLinearizedDeTurckVFPrincipal_add]
    rw [heq, partialDeriv_add (E := E)
          (fun y' => chartLinearizedDeTurckVFPrincipal (I := I) g g' α h₁ k y')
          (fun y' => chartLinearizedDeTurckVFPrincipal (I := I) g g' α h₂ k y')
          (chartLinearizedDeTurckVFPrincipal_differentiableAt (I := I) g g' α h₁ k hy)
          (chartLinearizedDeTurckVFPrincipal_differentiableAt (I := I) g g' α h₂ k hy)]
  have hsum1 : (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α k j y *
          partialDeriv (E := E) i
            (fun y' => chartLinearizedDeTurckVFPrincipal (I := I) g g' α (h₁ + h₂) k y')
            y) =
      (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α k j y *
          partialDeriv (E := E) i
            (fun y' => chartLinearizedDeTurckVFPrincipal (I := I) g g' α h₁ k y') y) +
      (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α k j y *
          partialDeriv (E := E) i
            (fun y' => chartLinearizedDeTurckVFPrincipal (I := I) g g' α h₂ k y') y) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hadd i k]; ring
  have hsum2 : (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α i k y *
          partialDeriv (E := E) j
            (fun y' => chartLinearizedDeTurckVFPrincipal (I := I) g g' α (h₁ + h₂) k y')
            y) =
      (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α i k y *
          partialDeriv (E := E) j
            (fun y' => chartLinearizedDeTurckVFPrincipal (I := I) g g' α h₁ k y') y) +
      (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α i k y *
          partialDeriv (E := E) j
            (fun y' => chartLinearizedDeTurckVFPrincipal (I := I) g g' α h₂ k y') y) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hadd j k]; ring
  rw [hsum1, hsum2]
  ring

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem chartDeTurckCorrSecondOrderPart_smul
    (g g' : SmoothRiemannianMetric I M) (α : M) (c : ℝ)
    (h : ChartMetricPerturbation E) (i j : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    chartDeTurckCorrSecondOrderPart (I := I) g g' α (c • h) i j y =
      c • chartDeTurckCorrSecondOrderPart (I := I) g g' α h i j y := by
  classical
  rw [chartDeTurckCorrSecondOrderPart_def, chartDeTurckCorrSecondOrderPart_def,
    smul_eq_mul]
  have hsmul : ∀ (d k : Fin (Module.finrank ℝ E)),
      partialDeriv (E := E) d
          (fun y' => chartLinearizedDeTurckVFPrincipal (I := I) g g' α (c • h) k y') y =
        c * partialDeriv (E := E) d
          (fun y' => chartLinearizedDeTurckVFPrincipal (I := I) g g' α h k y') y := by
    intro d k
    have heq : (fun y' => chartLinearizedDeTurckVFPrincipal (I := I) g g' α
          (c • h) k y') =
        fun y' => c • chartLinearizedDeTurckVFPrincipal (I := I) g g' α h k y' := by
      funext y'; rw [chartLinearizedDeTurckVFPrincipal_smul]
    rw [heq, partialDeriv_const_smul (E := E) c
          (fun y' => chartLinearizedDeTurckVFPrincipal (I := I) g g' α h k y')
          (chartLinearizedDeTurckVFPrincipal_differentiableAt (I := I) g g' α h k hy),
      smul_eq_mul]
  have hsum1 : (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α k j y *
          partialDeriv (E := E) i
            (fun y' => chartLinearizedDeTurckVFPrincipal (I := I) g g' α (c • h) k y')
            y) =
      c * ∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α k j y *
          partialDeriv (E := E) i
            (fun y' => chartLinearizedDeTurckVFPrincipal (I := I) g g' α h k y') y := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hsmul i k]; ring
  have hsum2 : (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α i k y *
          partialDeriv (E := E) j
            (fun y' => chartLinearizedDeTurckVFPrincipal (I := I) g g' α (c • h) k y')
            y) =
      c * ∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α i k y *
          partialDeriv (E := E) j
            (fun y' => chartLinearizedDeTurckVFPrincipal (I := I) g g' α h k y') y := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hsmul j k]; ring
  rw [hsum1, hsum2]
  ring

end DeTurckLinearization
end DeTurck
end PDE
end DifferentialGeometry
