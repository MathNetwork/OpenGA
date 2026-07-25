import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.InvGramPerturbation


noncomputable section

open Set Function
open scoped Topology ContDiff Matrix Manifold

namespace DifferentialGeometry
namespace PDE
namespace DeTurck
namespace RicciLinearization

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

namespace ChartMetricPerturbation

instance : Add (ChartMetricPerturbation E) :=
  ⟨fun h₁ h₂ =>
    { toFun := fun i j y => h₁ i j y + h₂ i j y
      symm' := fun i j y => by
        simp only [ChartMetricPerturbation.symm h₁ i j y, ChartMetricPerturbation.symm h₂ i j y]
      smooth' := fun i j => (h₁.smooth i j).add (h₂.smooth i j) }⟩

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma add_apply (h₁ h₂ : ChartMetricPerturbation E)
    (i j : Fin (Module.finrank ℝ E)) (y : E) :
    (h₁ + h₂) i j y = h₁ i j y + h₂ i j y := rfl

instance : SMul ℝ (ChartMetricPerturbation E) :=
  ⟨fun c h =>
    { toFun := fun i j y => c • h i j y
      symm' := fun i j y => by
        simp only [ChartMetricPerturbation.symm h i j y]
      smooth' := fun i j => (h.smooth i j).const_smul c }⟩

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma smul_apply (c : ℝ) (h : ChartMetricPerturbation E)
    (i j : Fin (Module.finrank ℝ E)) (y : E) :
    (c • h) i j y = c • h i j y := rfl

end ChartMetricPerturbation

def chartLinearizedChristoffelPrincipal (g : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (i j k : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
    chartInvGramOnE (I := I) g α k l y *
      (partialDeriv (E := E) i (h l j) y +
       partialDeriv (E := E) j (h l i) y -
       partialDeriv (E := E) l (h i j) y)

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
@[simp] lemma chartLinearizedChristoffelPrincipal_def
    (g : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (i j k : Fin (Module.finrank ℝ E)) (y : E) :
    chartLinearizedChristoffelPrincipal (I := I) g α h i j k y =
      (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g α k l y *
          (partialDeriv (E := E) i (h l j) y +
           partialDeriv (E := E) j (h l i) y -
           partialDeriv (E := E) l (h i j) y) := rfl

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem chartLinearizedChristoffelPrincipal_symm
    (g : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (i j k : Fin (Module.finrank ℝ E)) (y : E) :
    chartLinearizedChristoffelPrincipal (I := I) g α h i j k y =
      chartLinearizedChristoffelPrincipal (I := I) g α h j i k y := by
  classical
  rw [chartLinearizedChristoffelPrincipal_def, chartLinearizedChristoffelPrincipal_def]
  congr 1
  refine Finset.sum_congr rfl (fun l _ => ?_)
  congr 1
  rw [show partialDeriv (E := E) l (h i j) y =
        partialDeriv (E := E) l (h j i) y from by rw [h.symm_fun i j]]
  ring

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
@[simp] lemma chartLinearizedChristoffelPrincipal_zero
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j k : Fin (Module.finrank ℝ E)) (y : E) :
    chartLinearizedChristoffelPrincipal (I := I) g α
      (0 : ChartMetricPerturbation E) i j k y = 0 := by
  classical
  rw [chartLinearizedChristoffelPrincipal_def]
  have hzero : ∀ l : Fin (Module.finrank ℝ E),
      chartInvGramOnE (I := I) g α k l y *
        (partialDeriv (E := E) i ((0 : ChartMetricPerturbation E) l j) y +
         partialDeriv (E := E) j ((0 : ChartMetricPerturbation E) l i) y -
         partialDeriv (E := E) l ((0 : ChartMetricPerturbation E) i j) y) = 0 := by
    intro l
    have hlj : ((0 : ChartMetricPerturbation E) l j) = fun _ : E => (0 : ℝ) := rfl
    have hli : ((0 : ChartMetricPerturbation E) l i) = fun _ : E => (0 : ℝ) := rfl
    have hij : ((0 : ChartMetricPerturbation E) i j) = fun _ : E => (0 : ℝ) := rfl
    rw [hlj, hli, hij, partialDeriv_const, partialDeriv_const, partialDeriv_const]
    ring
  rw [Finset.sum_congr rfl (fun l _ => hzero l), Finset.sum_const_zero, mul_zero]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem chartLinearizedChristoffelPrincipal_add
    (g : SmoothRiemannianMetric I M) (α : M)
    (h₁ h₂ : ChartMetricPerturbation E) (i j k : Fin (Module.finrank ℝ E)) (y : E) :
    chartLinearizedChristoffelPrincipal (I := I) g α (h₁ + h₂) i j k y =
      chartLinearizedChristoffelPrincipal (I := I) g α h₁ i j k y +
        chartLinearizedChristoffelPrincipal (I := I) g α h₂ i j k y := by
  classical
  rw [chartLinearizedChristoffelPrincipal_def, chartLinearizedChristoffelPrincipal_def,
    chartLinearizedChristoffelPrincipal_def]
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl (fun l _ => ?_)
  have hi : partialDeriv (E := E) i ((h₁ + h₂) l j) y =
      partialDeriv (E := E) i (h₁ l j) y + partialDeriv (E := E) i (h₂ l j) y := by
    have heq : ((h₁ + h₂) l j) = fun y => h₁ l j y + h₂ l j y := rfl
    rw [heq, partialDeriv_add _ _ (h₁.differentiableAt l j y) (h₂.differentiableAt l j y)]
  have hj : partialDeriv (E := E) j ((h₁ + h₂) l i) y =
      partialDeriv (E := E) j (h₁ l i) y + partialDeriv (E := E) j (h₂ l i) y := by
    have heq : ((h₁ + h₂) l i) = fun y => h₁ l i y + h₂ l i y := rfl
    rw [heq, partialDeriv_add _ _ (h₁.differentiableAt l i y) (h₂.differentiableAt l i y)]
  have hl : partialDeriv (E := E) l ((h₁ + h₂) i j) y =
      partialDeriv (E := E) l (h₁ i j) y + partialDeriv (E := E) l (h₂ i j) y := by
    have heq : ((h₁ + h₂) i j) = fun y => h₁ i j y + h₂ i j y := rfl
    rw [heq, partialDeriv_add _ _ (h₁.differentiableAt i j y) (h₂.differentiableAt i j y)]
  rw [hi, hj, hl]
  ring

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem chartLinearizedChristoffelPrincipal_smul
    (g : SmoothRiemannianMetric I M) (α : M) (c : ℝ)
    (h : ChartMetricPerturbation E) (i j k : Fin (Module.finrank ℝ E)) (y : E) :
    chartLinearizedChristoffelPrincipal (I := I) g α (c • h) i j k y =
      c • chartLinearizedChristoffelPrincipal (I := I) g α h i j k y := by
  classical
  rw [chartLinearizedChristoffelPrincipal_def, chartLinearizedChristoffelPrincipal_def,
    smul_eq_mul]
  have hsummand : ∀ l : Fin (Module.finrank ℝ E),
      chartInvGramOnE (I := I) g α k l y *
        (partialDeriv (E := E) i ((c • h) l j) y +
         partialDeriv (E := E) j ((c • h) l i) y -
         partialDeriv (E := E) l ((c • h) i j) y) =
      c * (chartInvGramOnE (I := I) g α k l y *
        (partialDeriv (E := E) i (h l j) y +
         partialDeriv (E := E) j (h l i) y -
         partialDeriv (E := E) l (h i j) y)) := by
    intro l
    have hi : partialDeriv (E := E) i ((c • h) l j) y =
        c * partialDeriv (E := E) i (h l j) y := by
      have heq : ((c • h) l j) = fun y => c • h l j y := rfl
      rw [heq, partialDeriv_const_smul c _ (h.differentiableAt l j y), smul_eq_mul]
    have hj : partialDeriv (E := E) j ((c • h) l i) y =
        c * partialDeriv (E := E) j (h l i) y := by
      have heq : ((c • h) l i) = fun y => c • h l i y := rfl
      rw [heq, partialDeriv_const_smul c _ (h.differentiableAt l i y), smul_eq_mul]
    have hl : partialDeriv (E := E) l ((c • h) i j) y =
        c * partialDeriv (E := E) l (h i j) y := by
      have heq : ((c • h) i j) = fun y => c • h i j y := rfl
      rw [heq, partialDeriv_const_smul c _ (h.differentiableAt i j y), smul_eq_mul]
    rw [hi, hj, hl]
    ring
  rw [Finset.sum_congr rfl (fun l _ => hsummand l), ← Finset.mul_sum]
  ring

omit [NeZero (Module.finrank ℝ E)] in
private lemma partialDeriv_contDiff_of_contDiff
    {u : E → ℝ} (hu : ContDiff ℝ ∞ u) (i : Fin (Module.finrank ℝ E)) :
    ContDiff ℝ ∞ (partialDeriv (E := E) i u) := by
  have hfderiv : ContDiff ℝ ∞ (fderiv ℝ u) :=
    hu.fderiv_right (by rw [ENat.coe_top_add_one])
  unfold partialDeriv
  exact hfderiv.clm_apply contDiff_const

omit [NeZero (Module.finrank ℝ E)] in
private lemma partialDeriv_perturbation_contDiff
    (h : ChartMetricPerturbation E) (i a b : Fin (Module.finrank ℝ E)) :
    ContDiff ℝ ∞ (partialDeriv (E := E) i (h a b)) :=
  partialDeriv_contDiff_of_contDiff (h.smooth a b) i

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem chartLinearizedChristoffelPrincipal_contDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (i j k : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (fun y => chartLinearizedChristoffelPrincipal (I := I) g α h i j k y)
      (extChartAt I α).target := by
  classical
  have hsummand : ∀ l : Fin (Module.finrank ℝ E),
      ContDiffOn ℝ ∞
        (fun y => chartInvGramOnE (I := I) g α k l y *
          (partialDeriv (E := E) i (h l j) y +
           partialDeriv (E := E) j (h l i) y -
           partialDeriv (E := E) l (h i j) y))
        (extChartAt I α).target := by
    intro l
    have hG : ContDiffOn ℝ ∞ (chartInvGramOnE (I := I) g α k l)
        (extChartAt I α).target :=
      chartInvGramOnE_contDiffOn (I := I) g α k l
    have hdi : ContDiffOn ℝ ∞ (partialDeriv (E := E) i (h l j))
        (extChartAt I α).target :=
      (partialDeriv_perturbation_contDiff h i l j).contDiffOn
    have hdj : ContDiffOn ℝ ∞ (partialDeriv (E := E) j (h l i))
        (extChartAt I α).target :=
      (partialDeriv_perturbation_contDiff h j l i).contDiffOn
    have hdl : ContDiffOn ℝ ∞ (partialDeriv (E := E) l (h i j))
        (extChartAt I α).target :=
      (partialDeriv_perturbation_contDiff h l i j).contDiffOn
    exact hG.mul ((hdi.add hdj).sub hdl)
  have hsum : ContDiffOn ℝ ∞
      (fun y => ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g α k l y *
          (partialDeriv (E := E) i (h l j) y +
           partialDeriv (E := E) j (h l i) y -
           partialDeriv (E := E) l (h i j) y))
      (extChartAt I α).target :=
    ContDiffOn.sum (fun l _ => hsummand l)
  have hresult : ContDiffOn ℝ ∞
      (fun y => (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g α k l y *
          (partialDeriv (E := E) i (h l j) y +
           partialDeriv (E := E) j (h l i) y -
           partialDeriv (E := E) l (h i j) y))
      (extChartAt I α).target :=
    contDiffOn_const.mul hsum
  refine hresult.congr (fun y _ => ?_)
  rw [chartLinearizedChristoffelPrincipal_def]

end RicciLinearization
end DeTurck
end PDE
end DifferentialGeometry
