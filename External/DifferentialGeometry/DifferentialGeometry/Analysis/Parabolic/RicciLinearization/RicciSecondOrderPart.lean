import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.ChristoffelLinearization


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

section Differentiability

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma chartInvGramOnE_differentiableAt_interior
    (g : SmoothRiemannianMetric I M) (α : M)
    (j l : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    DifferentiableAt ℝ (chartInvGramOnE (I := I) g α j l) y := by
  have hcd : ContDiffOn ℝ ∞ (chartInvGramOnE (I := I) g α j l)
      (extChartAt I α).target := chartInvGramOnE_contDiffOn (I := I) g α j l
  have hcd_int : ContDiffOn ℝ ∞ (chartInvGramOnE (I := I) g α j l)
      (interior (extChartAt I α).target) := hcd.mono interior_subset
  have hop : IsOpen (interior (extChartAt I α).target) := isOpen_interior
  have hat : ContDiffAt ℝ ∞ (chartInvGramOnE (I := I) g α j l) y :=
    hcd_int.contDiffAt (hop.mem_nhds hy)
  exact hat.differentiableAt (by simp)

omit [NeZero (Module.finrank ℝ E)] in
lemma partialDeriv_contDiff_of_contDiff
    {u : E → ℝ} (hu : ContDiff ℝ ∞ u) (i : Fin (Module.finrank ℝ E)) :
    ContDiff ℝ ∞ (partialDeriv (E := E) i u) := by
  have hfderiv : ContDiff ℝ ∞ (fderiv ℝ u) :=
    hu.fderiv_right (by rw [ENat.coe_top_add_one])
  unfold partialDeriv
  exact hfderiv.clm_apply contDiff_const

omit [NeZero (Module.finrank ℝ E)] in
lemma partialDeriv_perturbation_contDiff
    (h : ChartMetricPerturbation E) (i a b : Fin (Module.finrank ℝ E)) :
    ContDiff ℝ ∞ (partialDeriv (E := E) i (h a b)) :=
  partialDeriv_contDiff_of_contDiff (h.smooth a b) i

omit [NeZero (Module.finrank ℝ E)] in
lemma partialDeriv_perturbation_differentiableAt
    (h : ChartMetricPerturbation E) (i a b : Fin (Module.finrank ℝ E)) (y : E) :
    DifferentiableAt ℝ (partialDeriv (E := E) i (h a b)) y :=
  ((partialDeriv_perturbation_contDiff h i a b).differentiable (by simp)).differentiableAt

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma chartLinearizedChristoffelPrincipal_differentiableAt
    (g : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (i j k : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    DifferentiableAt ℝ
      (fun y' => chartLinearizedChristoffelPrincipal (I := I) g α h i j k y') y := by
  have hcd : ContDiffOn ℝ ∞
      (fun y' => chartLinearizedChristoffelPrincipal (I := I) g α h i j k y')
      (interior (extChartAt I α).target) :=
    (chartLinearizedChristoffelPrincipal_contDiffOn (I := I) g α h i j k).mono
      interior_subset
  have hat : ContDiffAt ℝ ∞
      (fun y' => chartLinearizedChristoffelPrincipal (I := I) g α h i j k y') y :=
    hcd.contDiffAt (isOpen_interior.mem_nhds hy)
  exact hat.differentiableAt (by simp)

omit [NeZero (Module.finrank ℝ E)] in
lemma partialDeriv_partialDeriv_perturbation_swap
    (h : ChartMetricPerturbation E) (a b p q : Fin (Module.finrank ℝ E)) (y : E) :
    partialDeriv (E := E) p (partialDeriv (E := E) q (h a b)) y =
      partialDeriv (E := E) q (partialDeriv (E := E) p (h a b)) y := by
  classical
  have hsmooth : ContDiff ℝ ∞ (h a b) := h.smooth a b
  have hcontDiffAt : ContDiffAt ℝ ∞ (h a b) y := hsmooth.contDiffAt
  have hsymm2 : IsSymmSndFDerivAt ℝ (h a b) y := by
    refine ContDiffAt.isSymmSndFDerivAt hcontDiffAt ?_
    rw [minSmoothness_of_isRCLikeNormedField]
    decide
  have hg_diff : DifferentiableAt ℝ (fderiv ℝ (h a b)) y := by
    have hfderiv : ContDiff ℝ ∞ (fderiv ℝ (h a b)) :=
      hsmooth.fderiv_right (by rw [ENat.coe_top_add_one])
    exact (hfderiv.differentiable (by simp)).differentiableAt
  have hkey : ∀ r s : Fin (Module.finrank ℝ E),
      partialDeriv (E := E) r (partialDeriv (E := E) s (h a b)) y =
        (fderiv ℝ (fderiv ℝ (h a b)) y ((chartModelBasis E) r))
          ((chartModelBasis E) s) := by
    intro r s
    unfold partialDeriv
    set L : (E →L[ℝ] ℝ) →L[ℝ] ℝ :=
      ContinuousLinearMap.apply ℝ ℝ ((chartModelBasis E) s)
    have hcomp_eq : (fun z : E => fderiv ℝ (h a b) z ((chartModelBasis E) s)) =
        L ∘ (fderiv ℝ (h a b)) := by
      funext z; rfl
    rw [hcomp_eq, fderiv_comp y L.differentiableAt hg_diff, L.fderiv]
    rfl
  rw [hkey p q, hkey q p]
  exact hsymm2 _ _

end Differentiability

def chartRicciSecondOrderPart (g : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (i k : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  ∑ j : Fin (Module.finrank ℝ E),
    (partialDeriv (E := E) j
        (fun y' => chartLinearizedChristoffelPrincipal (I := I) g α h i k j y') y -
      partialDeriv (E := E) k
        (fun y' => chartLinearizedChristoffelPrincipal (I := I) g α h i j j y') y)

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
@[simp] lemma chartRicciSecondOrderPart_def
    (g : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (i k : Fin (Module.finrank ℝ E)) (y : E) :
    chartRicciSecondOrderPart (I := I) g α h i k y =
      ∑ j : Fin (Module.finrank ℝ E),
        (partialDeriv (E := E) j
            (fun y' => chartLinearizedChristoffelPrincipal (I := I) g α h i k j y') y -
          partialDeriv (E := E) k
            (fun y' => chartLinearizedChristoffelPrincipal (I := I) g α h i j j y') y) :=
  rfl

def chartRicciSecondOrderPrincipalSymbol (g : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (i k : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  (1 / 2 : ℝ) * ∑ j : Fin (Module.finrank ℝ E),
    ∑ l : Fin (Module.finrank ℝ E),
      chartInvGramOnE (I := I) g α j l y *
        (partialDeriv (E := E) j (partialDeriv (E := E) i (h l k)) y +
         partialDeriv (E := E) k (partialDeriv (E := E) l (h i j)) y -
         partialDeriv (E := E) j (partialDeriv (E := E) l (h i k)) y -
         partialDeriv (E := E) k (partialDeriv (E := E) i (h l j)) y)

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
@[simp] lemma chartRicciSecondOrderPrincipalSymbol_def
    (g : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (i k : Fin (Module.finrank ℝ E)) (y : E) :
    chartRicciSecondOrderPrincipalSymbol (I := I) g α h i k y =
      (1 / 2 : ℝ) * ∑ j : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j l y *
            (partialDeriv (E := E) j (partialDeriv (E := E) i (h l k)) y +
             partialDeriv (E := E) k (partialDeriv (E := E) l (h i j)) y -
             partialDeriv (E := E) j (partialDeriv (E := E) l (h i k)) y -
             partialDeriv (E := E) k (partialDeriv (E := E) i (h l j)) y) :=
  rfl

def chartRicciFirstOrderRemainder (g : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (i k : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  (1 / 2 : ℝ) * ∑ j : Fin (Module.finrank ℝ E),
    ∑ l : Fin (Module.finrank ℝ E),
      partialDeriv (E := E) j (chartInvGramOnE (I := I) g α j l) y *
        (partialDeriv (E := E) i (h l k) y +
         partialDeriv (E := E) k (h l i) y -
         partialDeriv (E := E) l (h i k) y) -
  (1 / 2 : ℝ) * ∑ j : Fin (Module.finrank ℝ E),
    ∑ l : Fin (Module.finrank ℝ E),
      partialDeriv (E := E) k (chartInvGramOnE (I := I) g α j l) y *
        (partialDeriv (E := E) i (h l j) y +
         partialDeriv (E := E) j (h l i) y -
         partialDeriv (E := E) l (h i j) y)

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
@[simp] lemma chartRicciFirstOrderRemainder_def
    (g : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (i k : Fin (Module.finrank ℝ E)) (y : E) :
    chartRicciFirstOrderRemainder (I := I) g α h i k y =
      (1 / 2 : ℝ) * ∑ j : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          partialDeriv (E := E) j (chartInvGramOnE (I := I) g α j l) y *
            (partialDeriv (E := E) i (h l k) y +
             partialDeriv (E := E) k (h l i) y -
             partialDeriv (E := E) l (h i k) y) -
      (1 / 2 : ℝ) * ∑ j : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          partialDeriv (E := E) k (chartInvGramOnE (I := I) g α j l) y *
            (partialDeriv (E := E) i (h l j) y +
             partialDeriv (E := E) j (h l i) y -
             partialDeriv (E := E) l (h i j) y) :=
  rfl

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma partialDeriv_chartLinearizedChristoffelPrincipal
    (g : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (a b j d : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    partialDeriv (E := E) d
        (fun y' => chartLinearizedChristoffelPrincipal (I := I) g α h a b j y') y =
      (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
        (partialDeriv (E := E) d (chartInvGramOnE (I := I) g α j l) y *
            (partialDeriv (E := E) a (h l b) y +
             partialDeriv (E := E) b (h l a) y -
             partialDeriv (E := E) l (h a b) y) +
          chartInvGramOnE (I := I) g α j l y *
            (partialDeriv (E := E) d (partialDeriv (E := E) a (h l b)) y +
             partialDeriv (E := E) d (partialDeriv (E := E) b (h l a)) y -
             partialDeriv (E := E) d (partialDeriv (E := E) l (h a b)) y)) := by
  classical
  set S : Fin (Module.finrank ℝ E) → E → ℝ := fun l y' =>
    partialDeriv (E := E) a (h l b) y' +
      partialDeriv (E := E) b (h l a) y' -
      partialDeriv (E := E) l (h a b) y' with hS
  have hS_diff : ∀ l : Fin (Module.finrank ℝ E), DifferentiableAt ℝ (S l) y := by
    intro l
    have h1 : DifferentiableAt ℝ (partialDeriv (E := E) a (h l b)) y :=
      partialDeriv_perturbation_differentiableAt h a l b y
    have h2 : DifferentiableAt ℝ (partialDeriv (E := E) b (h l a)) y :=
      partialDeriv_perturbation_differentiableAt h b l a y
    have h3 : DifferentiableAt ℝ (partialDeriv (E := E) l (h a b)) y :=
      partialDeriv_perturbation_differentiableAt h l a b y
    exact (h1.add h2).sub h3
  have hG_diff : ∀ l : Fin (Module.finrank ℝ E),
      DifferentiableAt ℝ (chartInvGramOnE (I := I) g α j l) y :=
    fun l => chartInvGramOnE_differentiableAt_interior (I := I) g α j l hy
  have hsummand_diff : ∀ l : Fin (Module.finrank ℝ E),
      DifferentiableAt ℝ
        (fun y' => chartInvGramOnE (I := I) g α j l y' * S l y') y :=
    fun l => (hG_diff l).mul (hS_diff l)
  have hrewrite : (fun y' => chartLinearizedChristoffelPrincipal (I := I) g α h a b j y') =
      fun y' => (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g α j l y' * S l y' := by
    funext y'
    rw [chartLinearizedChristoffelPrincipal_def]
  rw [hrewrite]
  rw [partialDeriv_const_mul (1 / 2 : ℝ)
        (fun y' => ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j l y' * S l y')
        (DifferentiableAt.fun_sum (fun l _ => hsummand_diff l))]
  congr 1
  rw [partialDeriv_sum Finset.univ
        (fun l y' => chartInvGramOnE (I := I) g α j l y' * S l y')
        (fun l _ => hsummand_diff l)]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [partialDeriv_mul (chartInvGramOnE (I := I) g α j l) (S l)
        (hG_diff l) (hS_diff l)]
  have hSderiv : partialDeriv (E := E) d (S l) y =
      partialDeriv (E := E) d (partialDeriv (E := E) a (h l b)) y +
        partialDeriv (E := E) d (partialDeriv (E := E) b (h l a)) y -
        partialDeriv (E := E) d (partialDeriv (E := E) l (h a b)) y := by
    have h1 : DifferentiableAt ℝ (partialDeriv (E := E) a (h l b)) y :=
      partialDeriv_perturbation_differentiableAt h a l b y
    have h2 : DifferentiableAt ℝ (partialDeriv (E := E) b (h l a)) y :=
      partialDeriv_perturbation_differentiableAt h b l a y
    have h3 : DifferentiableAt ℝ (partialDeriv (E := E) l (h a b)) y :=
      partialDeriv_perturbation_differentiableAt h l a b y
    rw [hS]
    rw [partialDeriv_sub (E := E)
          (fun y' => partialDeriv (E := E) a (h l b) y' +
            partialDeriv (E := E) b (h l a) y')
          (partialDeriv (E := E) l (h a b)) (h1.add h2) h3]
    rw [partialDeriv_add (E := E)
          (partialDeriv (E := E) a (h l b)) (partialDeriv (E := E) b (h l a)) h1 h2]
  rw [hSderiv, hS]

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem chartRicciSecondOrderPart_eq_principalSymbol_add_remainder
    (g : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (i k : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    chartRicciSecondOrderPart (I := I) g α h i k y =
      chartRicciSecondOrderPrincipalSymbol (I := I) g α h i k y +
        chartRicciFirstOrderRemainder (I := I) g α h i k y := by
  classical
  rw [chartRicciSecondOrderPart_def]
  have hexpand : ∀ j : Fin (Module.finrank ℝ E),
      partialDeriv (E := E) j
          (fun y' => chartLinearizedChristoffelPrincipal (I := I) g α h i k j y') y -
        partialDeriv (E := E) k
          (fun y' => chartLinearizedChristoffelPrincipal (I := I) g α h i j j y') y =
      ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
        (partialDeriv (E := E) j (chartInvGramOnE (I := I) g α j l) y *
            (partialDeriv (E := E) i (h l k) y +
             partialDeriv (E := E) k (h l i) y -
             partialDeriv (E := E) l (h i k) y) +
          chartInvGramOnE (I := I) g α j l y *
            (partialDeriv (E := E) j (partialDeriv (E := E) i (h l k)) y +
             partialDeriv (E := E) j (partialDeriv (E := E) k (h l i)) y -
             partialDeriv (E := E) j (partialDeriv (E := E) l (h i k)) y))) -
      ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
        (partialDeriv (E := E) k (chartInvGramOnE (I := I) g α j l) y *
            (partialDeriv (E := E) i (h l j) y +
             partialDeriv (E := E) j (h l i) y -
             partialDeriv (E := E) l (h i j) y) +
          chartInvGramOnE (I := I) g α j l y *
            (partialDeriv (E := E) k (partialDeriv (E := E) i (h l j)) y +
             partialDeriv (E := E) k (partialDeriv (E := E) j (h l i)) y -
             partialDeriv (E := E) k (partialDeriv (E := E) l (h i j)) y))) := by
    intro j
    rw [partialDeriv_chartLinearizedChristoffelPrincipal (I := I) g α h i k j j hy,
      partialDeriv_chartLinearizedChristoffelPrincipal (I := I) g α h i j j k hy]
  rw [Finset.sum_congr rfl (fun j _ => hexpand j)]
  have hsplit : ∀ j : Fin (Module.finrank ℝ E),
      ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
        (partialDeriv (E := E) j (chartInvGramOnE (I := I) g α j l) y *
            (partialDeriv (E := E) i (h l k) y +
             partialDeriv (E := E) k (h l i) y -
             partialDeriv (E := E) l (h i k) y) +
          chartInvGramOnE (I := I) g α j l y *
            (partialDeriv (E := E) j (partialDeriv (E := E) i (h l k)) y +
             partialDeriv (E := E) j (partialDeriv (E := E) k (h l i)) y -
             partialDeriv (E := E) j (partialDeriv (E := E) l (h i k)) y))) -
      ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
        (partialDeriv (E := E) k (chartInvGramOnE (I := I) g α j l) y *
            (partialDeriv (E := E) i (h l j) y +
             partialDeriv (E := E) j (h l i) y -
             partialDeriv (E := E) l (h i j) y) +
          chartInvGramOnE (I := I) g α j l y *
            (partialDeriv (E := E) k (partialDeriv (E := E) i (h l j)) y +
             partialDeriv (E := E) k (partialDeriv (E := E) j (h l i)) y -
             partialDeriv (E := E) k (partialDeriv (E := E) l (h i j)) y))) =
      ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j l y *
            (partialDeriv (E := E) j (partialDeriv (E := E) i (h l k)) y +
             partialDeriv (E := E) j (partialDeriv (E := E) k (h l i)) y -
             partialDeriv (E := E) j (partialDeriv (E := E) l (h i k)) y) -
        (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j l y *
            (partialDeriv (E := E) k (partialDeriv (E := E) i (h l j)) y +
             partialDeriv (E := E) k (partialDeriv (E := E) j (h l i)) y -
             partialDeriv (E := E) k (partialDeriv (E := E) l (h i j)) y)) +
      ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
          partialDeriv (E := E) j (chartInvGramOnE (I := I) g α j l) y *
            (partialDeriv (E := E) i (h l k) y +
             partialDeriv (E := E) k (h l i) y -
             partialDeriv (E := E) l (h i k) y) -
        (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
          partialDeriv (E := E) k (chartInvGramOnE (I := I) g α j l) y *
            (partialDeriv (E := E) i (h l j) y +
             partialDeriv (E := E) j (h l i) y -
             partialDeriv (E := E) l (h i j) y)) := by
    intro j
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, mul_add, mul_add]
    ring
  rw [Finset.sum_congr rfl (fun j _ => hsplit j)]
  rw [Finset.sum_add_distrib]
  have hrem : (∑ j : Fin (Module.finrank ℝ E),
      ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
          partialDeriv (E := E) j (chartInvGramOnE (I := I) g α j l) y *
            (partialDeriv (E := E) i (h l k) y +
             partialDeriv (E := E) k (h l i) y -
             partialDeriv (E := E) l (h i k) y) -
        (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
          partialDeriv (E := E) k (chartInvGramOnE (I := I) g α j l) y *
            (partialDeriv (E := E) i (h l j) y +
             partialDeriv (E := E) j (h l i) y -
             partialDeriv (E := E) l (h i j) y))) =
      chartRicciFirstOrderRemainder (I := I) g α h i k y := by
    rw [chartRicciFirstOrderRemainder_def]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hsymbol : (∑ j : Fin (Module.finrank ℝ E),
      ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j l y *
            (partialDeriv (E := E) j (partialDeriv (E := E) i (h l k)) y +
             partialDeriv (E := E) j (partialDeriv (E := E) k (h l i)) y -
             partialDeriv (E := E) j (partialDeriv (E := E) l (h i k)) y) -
        (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j l y *
            (partialDeriv (E := E) k (partialDeriv (E := E) i (h l j)) y +
             partialDeriv (E := E) k (partialDeriv (E := E) j (h l i)) y -
             partialDeriv (E := E) k (partialDeriv (E := E) l (h i j)) y))) =
      chartRicciSecondOrderPrincipalSymbol (I := I) g α h i k y := by
    rw [chartRicciSecondOrderPrincipalSymbol_def]
    have hcombine : ∀ j : Fin (Module.finrank ℝ E),
        ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α j l y *
              (partialDeriv (E := E) j (partialDeriv (E := E) i (h l k)) y +
               partialDeriv (E := E) j (partialDeriv (E := E) k (h l i)) y -
               partialDeriv (E := E) j (partialDeriv (E := E) l (h i k)) y) -
          (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α j l y *
              (partialDeriv (E := E) k (partialDeriv (E := E) i (h l j)) y +
               partialDeriv (E := E) k (partialDeriv (E := E) j (h l i)) y -
               partialDeriv (E := E) k (partialDeriv (E := E) l (h i j)) y)) =
        (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j l y *
            (partialDeriv (E := E) j (partialDeriv (E := E) i (h l k)) y +
             partialDeriv (E := E) k (partialDeriv (E := E) l (h i j)) y -
             partialDeriv (E := E) j (partialDeriv (E := E) l (h i k)) y -
             partialDeriv (E := E) k (partialDeriv (E := E) i (h l j)) y) := by
      intro j
      rw [← mul_sub, ← Finset.sum_sub_distrib]
      congr 1
      refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [partialDeriv_partialDeriv_perturbation_swap h l i j k y]
      ring
    rw [Finset.sum_congr rfl (fun j _ => hcombine j), ← Finset.mul_sum]
  rw [hrem, hsymbol, add_comm]

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem chartRicciSecondOrderPart_eq_principalSymbol_add_remainder_of_mem_source
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (i k : Fin (Module.finrank ℝ E))
    {x : M} (hx : x ∈ (chartAt H α).source) :
    chartRicciSecondOrderPart (I := I) g α h i k (extChartAt I α x) =
      chartRicciSecondOrderPrincipalSymbol (I := I) g α h i k (extChartAt I α x) +
        chartRicciFirstOrderRemainder (I := I) g α h i k (extChartAt I α x) := by
  have hxsrc : x ∈ (extChartAt I α).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hx
  have hx_target : extChartAt I α x ∈ (extChartAt I α).target :=
    (extChartAt I α).map_source hxsrc
  have hx_int : extChartAt I α x ∈ interior (extChartAt I α).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) α hx_target
  exact chartRicciSecondOrderPart_eq_principalSymbol_add_remainder (I := I) g α h i k hx_int

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem chartRicciFirstOrderRemainder_eq_first_order_sum
    (g : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (i k : Fin (Module.finrank ℝ E)) (y : E) :
    chartRicciFirstOrderRemainder (I := I) g α h i k y =
      ∑ j : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          (((1 / 2 : ℝ) * partialDeriv (E := E) j
                (chartInvGramOnE (I := I) g α j l) y) *
              partialDeriv (E := E) i (h l k) y +
            ((1 / 2 : ℝ) * partialDeriv (E := E) j
                (chartInvGramOnE (I := I) g α j l) y) *
              partialDeriv (E := E) k (h l i) y +
            (-(1 / 2 : ℝ) * partialDeriv (E := E) j
                (chartInvGramOnE (I := I) g α j l) y) *
              partialDeriv (E := E) l (h i k) y +
            (-(1 / 2 : ℝ) * partialDeriv (E := E) k
                (chartInvGramOnE (I := I) g α j l) y) *
              partialDeriv (E := E) i (h l j) y +
            (-(1 / 2 : ℝ) * partialDeriv (E := E) k
                (chartInvGramOnE (I := I) g α j l) y) *
              partialDeriv (E := E) j (h l i) y +
            ((1 / 2 : ℝ) * partialDeriv (E := E) k
                (chartInvGramOnE (I := I) g α j l) y) *
              partialDeriv (E := E) l (h i j) y) := by
  classical
  rw [chartRicciFirstOrderRemainder_def]
  simp only [Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  ring

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
@[simp] lemma chartRicciSecondOrderPart_zero
    (g : SmoothRiemannianMetric I M) (α : M)
    (i k : Fin (Module.finrank ℝ E)) (y : E) :
    chartRicciSecondOrderPart (I := I) g α
      (0 : ChartMetricPerturbation E) i k y = 0 := by
  classical
  rw [chartRicciSecondOrderPart_def]
  have hzero : ∀ j : Fin (Module.finrank ℝ E),
      partialDeriv (E := E) j
          (fun y' => chartLinearizedChristoffelPrincipal (I := I) g α
            (0 : ChartMetricPerturbation E) i k j y') y -
        partialDeriv (E := E) k
          (fun y' => chartLinearizedChristoffelPrincipal (I := I) g α
            (0 : ChartMetricPerturbation E) i j j y') y = 0 := by
    intro j
    have hik : (fun y' => chartLinearizedChristoffelPrincipal (I := I) g α
        (0 : ChartMetricPerturbation E) i k j y') = fun _ : E => (0 : ℝ) := by
      funext y'; rw [chartLinearizedChristoffelPrincipal_zero]
    have hij : (fun y' => chartLinearizedChristoffelPrincipal (I := I) g α
        (0 : ChartMetricPerturbation E) i j j y') = fun _ : E => (0 : ℝ) := by
      funext y'; rw [chartLinearizedChristoffelPrincipal_zero]
    rw [hik, hij, partialDeriv_const, partialDeriv_const, sub_zero]
  rw [Finset.sum_congr rfl (fun j _ => hzero j), Finset.sum_const_zero]

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem chartRicciSecondOrderPart_add
    (g : SmoothRiemannianMetric I M) (α : M)
    (h₁ h₂ : ChartMetricPerturbation E) (i k : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    chartRicciSecondOrderPart (I := I) g α (h₁ + h₂) i k y =
      chartRicciSecondOrderPart (I := I) g α h₁ i k y +
        chartRicciSecondOrderPart (I := I) g α h₂ i k y := by
  classical
  rw [chartRicciSecondOrderPart_def, chartRicciSecondOrderPart_def,
    chartRicciSecondOrderPart_def, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hadd_ik : partialDeriv (E := E) j
        (fun y' => chartLinearizedChristoffelPrincipal (I := I) g α (h₁ + h₂) i k j y')
        y =
      partialDeriv (E := E) j
        (fun y' => chartLinearizedChristoffelPrincipal (I := I) g α h₁ i k j y') y +
      partialDeriv (E := E) j
        (fun y' => chartLinearizedChristoffelPrincipal (I := I) g α h₂ i k j y') y := by
    have heq : (fun y' => chartLinearizedChristoffelPrincipal (I := I) g α
          (h₁ + h₂) i k j y') =
        fun y' => chartLinearizedChristoffelPrincipal (I := I) g α h₁ i k j y' +
          chartLinearizedChristoffelPrincipal (I := I) g α h₂ i k j y' := by
      funext y'; rw [chartLinearizedChristoffelPrincipal_add]
    rw [heq, partialDeriv_add (E := E)
          (fun y' => chartLinearizedChristoffelPrincipal (I := I) g α h₁ i k j y')
          (fun y' => chartLinearizedChristoffelPrincipal (I := I) g α h₂ i k j y')
          (chartLinearizedChristoffelPrincipal_differentiableAt (I := I) g α h₁ i k j hy)
          (chartLinearizedChristoffelPrincipal_differentiableAt (I := I) g α h₂ i k j hy)]
  have hadd_ij : partialDeriv (E := E) k
        (fun y' => chartLinearizedChristoffelPrincipal (I := I) g α (h₁ + h₂) i j j y')
        y =
      partialDeriv (E := E) k
        (fun y' => chartLinearizedChristoffelPrincipal (I := I) g α h₁ i j j y') y +
      partialDeriv (E := E) k
        (fun y' => chartLinearizedChristoffelPrincipal (I := I) g α h₂ i j j y') y := by
    have heq : (fun y' => chartLinearizedChristoffelPrincipal (I := I) g α
          (h₁ + h₂) i j j y') =
        fun y' => chartLinearizedChristoffelPrincipal (I := I) g α h₁ i j j y' +
          chartLinearizedChristoffelPrincipal (I := I) g α h₂ i j j y' := by
      funext y'; rw [chartLinearizedChristoffelPrincipal_add]
    rw [heq, partialDeriv_add (E := E)
          (fun y' => chartLinearizedChristoffelPrincipal (I := I) g α h₁ i j j y')
          (fun y' => chartLinearizedChristoffelPrincipal (I := I) g α h₂ i j j y')
          (chartLinearizedChristoffelPrincipal_differentiableAt (I := I) g α h₁ i j j hy)
          (chartLinearizedChristoffelPrincipal_differentiableAt (I := I) g α h₂ i j j hy)]
  rw [hadd_ik, hadd_ij]
  ring

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem chartRicciSecondOrderPart_smul
    (g : SmoothRiemannianMetric I M) (α : M) (c : ℝ)
    (h : ChartMetricPerturbation E) (i k : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    chartRicciSecondOrderPart (I := I) g α (c • h) i k y =
      c • chartRicciSecondOrderPart (I := I) g α h i k y := by
  classical
  rw [chartRicciSecondOrderPart_def, chartRicciSecondOrderPart_def, smul_eq_mul,
    Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hsmul_ik : partialDeriv (E := E) j
        (fun y' => chartLinearizedChristoffelPrincipal (I := I) g α (c • h) i k j y')
        y =
      c * partialDeriv (E := E) j
        (fun y' => chartLinearizedChristoffelPrincipal (I := I) g α h i k j y') y := by
    have heq : (fun y' => chartLinearizedChristoffelPrincipal (I := I) g α
          (c • h) i k j y') =
        fun y' => c • chartLinearizedChristoffelPrincipal (I := I) g α h i k j y' := by
      funext y'; rw [chartLinearizedChristoffelPrincipal_smul]
    rw [heq, partialDeriv_const_smul (E := E) c
          (fun y' => chartLinearizedChristoffelPrincipal (I := I) g α h i k j y')
          (chartLinearizedChristoffelPrincipal_differentiableAt (I := I) g α h i k j hy),
      smul_eq_mul]
  have hsmul_ij : partialDeriv (E := E) k
        (fun y' => chartLinearizedChristoffelPrincipal (I := I) g α (c • h) i j j y')
        y =
      c * partialDeriv (E := E) k
        (fun y' => chartLinearizedChristoffelPrincipal (I := I) g α h i j j y') y := by
    have heq : (fun y' => chartLinearizedChristoffelPrincipal (I := I) g α
          (c • h) i j j y') =
        fun y' => c • chartLinearizedChristoffelPrincipal (I := I) g α h i j j y' := by
      funext y'; rw [chartLinearizedChristoffelPrincipal_smul]
    rw [heq, partialDeriv_const_smul (E := E) c
          (fun y' => chartLinearizedChristoffelPrincipal (I := I) g α h i j j y')
          (chartLinearizedChristoffelPrincipal_differentiableAt (I := I) g α h i j j hy),
      smul_eq_mul]
  rw [hsmul_ik, hsmul_ij]
  ring

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
@[simp] lemma chartRicciSecondOrderPrincipalSymbol_zero
    (g : SmoothRiemannianMetric I M) (α : M)
    (i k : Fin (Module.finrank ℝ E)) (y : E) :
    chartRicciSecondOrderPrincipalSymbol (I := I) g α
      (0 : ChartMetricPerturbation E) i k y = 0 := by
  classical
  rw [chartRicciSecondOrderPrincipalSymbol_def]
  have hiter : ∀ p q a b : Fin (Module.finrank ℝ E),
      partialDeriv (E := E) p
          (partialDeriv (E := E) q ((0 : ChartMetricPerturbation E) a b)) y = 0 := by
    intro p q a b
    have hinner : partialDeriv (E := E) q ((0 : ChartMetricPerturbation E) a b) =
        fun _ : E => (0 : ℝ) := by
      funext y'
      have hconst : ((0 : ChartMetricPerturbation E) a b) = fun _ : E => (0 : ℝ) := rfl
      rw [hconst, partialDeriv_const]
    rw [hinner, partialDeriv_const]
  have hzero : ∀ j l : Fin (Module.finrank ℝ E),
      chartInvGramOnE (I := I) g α j l y *
        (partialDeriv (E := E) j (partialDeriv (E := E) i
            ((0 : ChartMetricPerturbation E) l k)) y +
         partialDeriv (E := E) k (partialDeriv (E := E) l
            ((0 : ChartMetricPerturbation E) i j)) y -
         partialDeriv (E := E) j (partialDeriv (E := E) l
            ((0 : ChartMetricPerturbation E) i k)) y -
         partialDeriv (E := E) k (partialDeriv (E := E) i
            ((0 : ChartMetricPerturbation E) l j)) y) = 0 := by
    intro j l
    rw [hiter j i l k, hiter k l i j, hiter j l i k, hiter k i l j]
    ring
  rw [Finset.sum_congr rfl (fun j _ =>
    Finset.sum_congr rfl (fun l _ => hzero j l))]
  rw [Finset.sum_const_zero, Finset.sum_const_zero, mul_zero]

omit [NeZero (Module.finrank ℝ E)] in
private lemma partialDeriv_partialDeriv_add_apply
    (h₁ h₂ : ChartMetricPerturbation E) (p q a b : Fin (Module.finrank ℝ E)) (y : E) :
    partialDeriv (E := E) p (partialDeriv (E := E) q ((h₁ + h₂) a b)) y =
      partialDeriv (E := E) p (partialDeriv (E := E) q (h₁ a b)) y +
        partialDeriv (E := E) p (partialDeriv (E := E) q (h₂ a b)) y := by
  have hinner : partialDeriv (E := E) q ((h₁ + h₂) a b) =
      fun y' => partialDeriv (E := E) q (h₁ a b) y' +
        partialDeriv (E := E) q (h₂ a b) y' := by
    funext y'
    have heq : ((h₁ + h₂) a b) = fun y'' => h₁ a b y'' + h₂ a b y'' := rfl
    rw [heq, partialDeriv_add (E := E) (h₁ a b) (h₂ a b)
          (h₁.differentiableAt a b y') (h₂.differentiableAt a b y')]
  rw [hinner, partialDeriv_add (E := E)
        (partialDeriv (E := E) q (h₁ a b)) (partialDeriv (E := E) q (h₂ a b))
        (partialDeriv_perturbation_differentiableAt h₁ q a b y)
        (partialDeriv_perturbation_differentiableAt h₂ q a b y)]

omit [NeZero (Module.finrank ℝ E)] in
private lemma partialDeriv_partialDeriv_smul_apply
    (c : ℝ) (h : ChartMetricPerturbation E) (p q a b : Fin (Module.finrank ℝ E)) (y : E) :
    partialDeriv (E := E) p (partialDeriv (E := E) q ((c • h) a b)) y =
      c * partialDeriv (E := E) p (partialDeriv (E := E) q (h a b)) y := by
  have hinner : partialDeriv (E := E) q ((c • h) a b) =
      fun y' => c • partialDeriv (E := E) q (h a b) y' := by
    funext y'
    have heq : ((c • h) a b) = fun y'' => c • h a b y'' := rfl
    rw [heq, partialDeriv_const_smul (E := E) c (h a b) (h.differentiableAt a b y')]
  rw [hinner, partialDeriv_const_smul (E := E) c
        (partialDeriv (E := E) q (h a b))
        (partialDeriv_perturbation_differentiableAt h q a b y), smul_eq_mul]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem chartRicciSecondOrderPrincipalSymbol_add
    (g : SmoothRiemannianMetric I M) (α : M)
    (h₁ h₂ : ChartMetricPerturbation E) (i k : Fin (Module.finrank ℝ E)) (y : E) :
    chartRicciSecondOrderPrincipalSymbol (I := I) g α (h₁ + h₂) i k y =
      chartRicciSecondOrderPrincipalSymbol (I := I) g α h₁ i k y +
        chartRicciSecondOrderPrincipalSymbol (I := I) g α h₂ i k y := by
  classical
  rw [chartRicciSecondOrderPrincipalSymbol_def, chartRicciSecondOrderPrincipalSymbol_def,
    chartRicciSecondOrderPrincipalSymbol_def, ← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [partialDeriv_partialDeriv_add_apply h₁ h₂ j i l k y,
    partialDeriv_partialDeriv_add_apply h₁ h₂ k l i j y,
    partialDeriv_partialDeriv_add_apply h₁ h₂ j l i k y,
    partialDeriv_partialDeriv_add_apply h₁ h₂ k i l j y]
  ring

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem chartRicciSecondOrderPrincipalSymbol_smul
    (g : SmoothRiemannianMetric I M) (α : M) (c : ℝ)
    (h : ChartMetricPerturbation E) (i k : Fin (Module.finrank ℝ E)) (y : E) :
    chartRicciSecondOrderPrincipalSymbol (I := I) g α (c • h) i k y =
      c • chartRicciSecondOrderPrincipalSymbol (I := I) g α h i k y := by
  classical
  rw [chartRicciSecondOrderPrincipalSymbol_def, chartRicciSecondOrderPrincipalSymbol_def,
    smul_eq_mul]
  have hsummand : ∀ j l : Fin (Module.finrank ℝ E),
      chartInvGramOnE (I := I) g α j l y *
        (partialDeriv (E := E) j (partialDeriv (E := E) i ((c • h) l k)) y +
         partialDeriv (E := E) k (partialDeriv (E := E) l ((c • h) i j)) y -
         partialDeriv (E := E) j (partialDeriv (E := E) l ((c • h) i k)) y -
         partialDeriv (E := E) k (partialDeriv (E := E) i ((c • h) l j)) y) =
      c * (chartInvGramOnE (I := I) g α j l y *
        (partialDeriv (E := E) j (partialDeriv (E := E) i (h l k)) y +
         partialDeriv (E := E) k (partialDeriv (E := E) l (h i j)) y -
         partialDeriv (E := E) j (partialDeriv (E := E) l (h i k)) y -
         partialDeriv (E := E) k (partialDeriv (E := E) i (h l j)) y)) := by
    intro j l
    rw [partialDeriv_partialDeriv_smul_apply c h j i l k y,
      partialDeriv_partialDeriv_smul_apply c h k l i j y,
      partialDeriv_partialDeriv_smul_apply c h j l i k y,
      partialDeriv_partialDeriv_smul_apply c h k i l j y]
    ring
  rw [Finset.sum_congr rfl (fun j _ =>
    Finset.sum_congr rfl (fun l _ => hsummand j l))]
  have hinner : ∀ j : Fin (Module.finrank ℝ E),
      (∑ l : Fin (Module.finrank ℝ E),
        c * (chartInvGramOnE (I := I) g α j l y *
          (partialDeriv (E := E) j (partialDeriv (E := E) i (h l k)) y +
           partialDeriv (E := E) k (partialDeriv (E := E) l (h i j)) y -
           partialDeriv (E := E) j (partialDeriv (E := E) l (h i k)) y -
           partialDeriv (E := E) k (partialDeriv (E := E) i (h l j)) y))) =
      c * ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g α j l y *
          (partialDeriv (E := E) j (partialDeriv (E := E) i (h l k)) y +
           partialDeriv (E := E) k (partialDeriv (E := E) l (h i j)) y -
           partialDeriv (E := E) j (partialDeriv (E := E) l (h i k)) y -
           partialDeriv (E := E) k (partialDeriv (E := E) i (h l j)) y) :=
    fun j => by rw [← Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun j _ => hinner j), ← Finset.mul_sum]
  ring

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
@[simp] lemma chartRicciFirstOrderRemainder_zero
    (g : SmoothRiemannianMetric I M) (α : M)
    (i k : Fin (Module.finrank ℝ E)) (y : E) :
    chartRicciFirstOrderRemainder (I := I) g α
      (0 : ChartMetricPerturbation E) i k y = 0 := by
  classical
  rw [chartRicciFirstOrderRemainder_def]
  have hzero1 : ∀ j l : Fin (Module.finrank ℝ E),
      partialDeriv (E := E) j (chartInvGramOnE (I := I) g α j l) y *
        (partialDeriv (E := E) i ((0 : ChartMetricPerturbation E) l k) y +
         partialDeriv (E := E) k ((0 : ChartMetricPerturbation E) l i) y -
         partialDeriv (E := E) l ((0 : ChartMetricPerturbation E) i k) y) = 0 := by
    intro j l
    have e1 : ((0 : ChartMetricPerturbation E) l k) = fun _ : E => (0 : ℝ) := rfl
    have e2 : ((0 : ChartMetricPerturbation E) l i) = fun _ : E => (0 : ℝ) := rfl
    have e3 : ((0 : ChartMetricPerturbation E) i k) = fun _ : E => (0 : ℝ) := rfl
    rw [e1, e2, e3]
    simp only [partialDeriv_const]
    ring
  have hzero2 : ∀ j l : Fin (Module.finrank ℝ E),
      partialDeriv (E := E) k (chartInvGramOnE (I := I) g α j l) y *
        (partialDeriv (E := E) i ((0 : ChartMetricPerturbation E) l j) y +
         partialDeriv (E := E) j ((0 : ChartMetricPerturbation E) l i) y -
         partialDeriv (E := E) l ((0 : ChartMetricPerturbation E) i j) y) = 0 := by
    intro j l
    have e1 : ((0 : ChartMetricPerturbation E) l j) = fun _ : E => (0 : ℝ) := rfl
    have e2 : ((0 : ChartMetricPerturbation E) l i) = fun _ : E => (0 : ℝ) := rfl
    have e3 : ((0 : ChartMetricPerturbation E) i j) = fun _ : E => (0 : ℝ) := rfl
    rw [e1, e2, e3]
    simp only [partialDeriv_const]
    ring
  rw [Finset.sum_congr rfl (fun j _ =>
    Finset.sum_congr rfl (fun l _ => hzero1 j l))]
  rw [Finset.sum_congr rfl (fun j _ =>
    Finset.sum_congr rfl (fun l _ => hzero2 j l))]
  simp

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem chartRicciFirstOrderRemainder_add
    (g : SmoothRiemannianMetric I M) (α : M)
    (h₁ h₂ : ChartMetricPerturbation E) (i k : Fin (Module.finrank ℝ E)) (y : E) :
    chartRicciFirstOrderRemainder (I := I) g α (h₁ + h₂) i k y =
      chartRicciFirstOrderRemainder (I := I) g α h₁ i k y +
        chartRicciFirstOrderRemainder (I := I) g α h₂ i k y := by
  classical
  rw [chartRicciFirstOrderRemainder_def, chartRicciFirstOrderRemainder_def,
    chartRicciFirstOrderRemainder_def]
  have hsummand1 : ∀ j l : Fin (Module.finrank ℝ E),
      partialDeriv (E := E) j (chartInvGramOnE (I := I) g α j l) y *
        (partialDeriv (E := E) i ((h₁ + h₂) l k) y +
         partialDeriv (E := E) k ((h₁ + h₂) l i) y -
         partialDeriv (E := E) l ((h₁ + h₂) i k) y) =
      partialDeriv (E := E) j (chartInvGramOnE (I := I) g α j l) y *
        (partialDeriv (E := E) i (h₁ l k) y +
         partialDeriv (E := E) k (h₁ l i) y -
         partialDeriv (E := E) l (h₁ i k) y) +
      partialDeriv (E := E) j (chartInvGramOnE (I := I) g α j l) y *
        (partialDeriv (E := E) i (h₂ l k) y +
         partialDeriv (E := E) k (h₂ l i) y -
         partialDeriv (E := E) l (h₂ i k) y) := by
    intro j l
    have ea : partialDeriv (E := E) i ((h₁ + h₂) l k) y =
        partialDeriv (E := E) i (h₁ l k) y + partialDeriv (E := E) i (h₂ l k) y := by
      have heq : ((h₁ + h₂) l k) = fun y'' => h₁ l k y'' + h₂ l k y'' := rfl
      rw [heq, partialDeriv_add (E := E) (h₁ l k) (h₂ l k)
            (h₁.differentiableAt l k y) (h₂.differentiableAt l k y)]
    have eb : partialDeriv (E := E) k ((h₁ + h₂) l i) y =
        partialDeriv (E := E) k (h₁ l i) y + partialDeriv (E := E) k (h₂ l i) y := by
      have heq : ((h₁ + h₂) l i) = fun y'' => h₁ l i y'' + h₂ l i y'' := rfl
      rw [heq, partialDeriv_add (E := E) (h₁ l i) (h₂ l i)
            (h₁.differentiableAt l i y) (h₂.differentiableAt l i y)]
    have ec : partialDeriv (E := E) l ((h₁ + h₂) i k) y =
        partialDeriv (E := E) l (h₁ i k) y + partialDeriv (E := E) l (h₂ i k) y := by
      have heq : ((h₁ + h₂) i k) = fun y'' => h₁ i k y'' + h₂ i k y'' := rfl
      rw [heq, partialDeriv_add (E := E) (h₁ i k) (h₂ i k)
            (h₁.differentiableAt i k y) (h₂.differentiableAt i k y)]
    rw [ea, eb, ec]
    ring
  have hsummand2 : ∀ j l : Fin (Module.finrank ℝ E),
      partialDeriv (E := E) k (chartInvGramOnE (I := I) g α j l) y *
        (partialDeriv (E := E) i ((h₁ + h₂) l j) y +
         partialDeriv (E := E) j ((h₁ + h₂) l i) y -
         partialDeriv (E := E) l ((h₁ + h₂) i j) y) =
      partialDeriv (E := E) k (chartInvGramOnE (I := I) g α j l) y *
        (partialDeriv (E := E) i (h₁ l j) y +
         partialDeriv (E := E) j (h₁ l i) y -
         partialDeriv (E := E) l (h₁ i j) y) +
      partialDeriv (E := E) k (chartInvGramOnE (I := I) g α j l) y *
        (partialDeriv (E := E) i (h₂ l j) y +
         partialDeriv (E := E) j (h₂ l i) y -
         partialDeriv (E := E) l (h₂ i j) y) := by
    intro j l
    have ea : partialDeriv (E := E) i ((h₁ + h₂) l j) y =
        partialDeriv (E := E) i (h₁ l j) y + partialDeriv (E := E) i (h₂ l j) y := by
      have heq : ((h₁ + h₂) l j) = fun y'' => h₁ l j y'' + h₂ l j y'' := rfl
      rw [heq, partialDeriv_add (E := E) (h₁ l j) (h₂ l j)
            (h₁.differentiableAt l j y) (h₂.differentiableAt l j y)]
    have eb : partialDeriv (E := E) j ((h₁ + h₂) l i) y =
        partialDeriv (E := E) j (h₁ l i) y + partialDeriv (E := E) j (h₂ l i) y := by
      have heq : ((h₁ + h₂) l i) = fun y'' => h₁ l i y'' + h₂ l i y'' := rfl
      rw [heq, partialDeriv_add (E := E) (h₁ l i) (h₂ l i)
            (h₁.differentiableAt l i y) (h₂.differentiableAt l i y)]
    have ec : partialDeriv (E := E) l ((h₁ + h₂) i j) y =
        partialDeriv (E := E) l (h₁ i j) y + partialDeriv (E := E) l (h₂ i j) y := by
      have heq : ((h₁ + h₂) i j) = fun y'' => h₁ i j y'' + h₂ i j y'' := rfl
      rw [heq, partialDeriv_add (E := E) (h₁ i j) (h₂ i j)
            (h₁.differentiableAt i j y) (h₂.differentiableAt i j y)]
    rw [ea, eb, ec]
    ring
  rw [Finset.sum_congr rfl (fun j _ =>
        Finset.sum_congr rfl (fun l _ => hsummand1 j l)),
    Finset.sum_congr rfl (fun j _ =>
        Finset.sum_congr rfl (fun l _ => hsummand2 j l))]
  rw [Finset.sum_congr rfl (fun j _ => Finset.sum_add_distrib),
    Finset.sum_congr rfl (fun j _ => Finset.sum_add_distrib),
    Finset.sum_add_distrib, Finset.sum_add_distrib, mul_add, mul_add]
  ring

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem chartRicciFirstOrderRemainder_smul
    (g : SmoothRiemannianMetric I M) (α : M) (c : ℝ)
    (h : ChartMetricPerturbation E) (i k : Fin (Module.finrank ℝ E)) (y : E) :
    chartRicciFirstOrderRemainder (I := I) g α (c • h) i k y =
      c • chartRicciFirstOrderRemainder (I := I) g α h i k y := by
  classical
  rw [chartRicciFirstOrderRemainder_def, chartRicciFirstOrderRemainder_def, smul_eq_mul]
  have hsummand1 : ∀ j l : Fin (Module.finrank ℝ E),
      partialDeriv (E := E) j (chartInvGramOnE (I := I) g α j l) y *
        (partialDeriv (E := E) i ((c • h) l k) y +
         partialDeriv (E := E) k ((c • h) l i) y -
         partialDeriv (E := E) l ((c • h) i k) y) =
      c * (partialDeriv (E := E) j (chartInvGramOnE (I := I) g α j l) y *
        (partialDeriv (E := E) i (h l k) y +
         partialDeriv (E := E) k (h l i) y -
         partialDeriv (E := E) l (h i k) y)) := by
    intro j l
    have ea : partialDeriv (E := E) i ((c • h) l k) y =
        c * partialDeriv (E := E) i (h l k) y := by
      have heq : ((c • h) l k) = fun y'' => c • h l k y'' := rfl
      rw [heq, partialDeriv_const_smul (E := E) c (h l k) (h.differentiableAt l k y),
        smul_eq_mul]
    have eb : partialDeriv (E := E) k ((c • h) l i) y =
        c * partialDeriv (E := E) k (h l i) y := by
      have heq : ((c • h) l i) = fun y'' => c • h l i y'' := rfl
      rw [heq, partialDeriv_const_smul (E := E) c (h l i) (h.differentiableAt l i y),
        smul_eq_mul]
    have ec : partialDeriv (E := E) l ((c • h) i k) y =
        c * partialDeriv (E := E) l (h i k) y := by
      have heq : ((c • h) i k) = fun y'' => c • h i k y'' := rfl
      rw [heq, partialDeriv_const_smul (E := E) c (h i k) (h.differentiableAt i k y),
        smul_eq_mul]
    rw [ea, eb, ec]
    ring
  have hsummand2 : ∀ j l : Fin (Module.finrank ℝ E),
      partialDeriv (E := E) k (chartInvGramOnE (I := I) g α j l) y *
        (partialDeriv (E := E) i ((c • h) l j) y +
         partialDeriv (E := E) j ((c • h) l i) y -
         partialDeriv (E := E) l ((c • h) i j) y) =
      c * (partialDeriv (E := E) k (chartInvGramOnE (I := I) g α j l) y *
        (partialDeriv (E := E) i (h l j) y +
         partialDeriv (E := E) j (h l i) y -
         partialDeriv (E := E) l (h i j) y)) := by
    intro j l
    have ea : partialDeriv (E := E) i ((c • h) l j) y =
        c * partialDeriv (E := E) i (h l j) y := by
      have heq : ((c • h) l j) = fun y'' => c • h l j y'' := rfl
      rw [heq, partialDeriv_const_smul (E := E) c (h l j) (h.differentiableAt l j y),
        smul_eq_mul]
    have eb : partialDeriv (E := E) j ((c • h) l i) y =
        c * partialDeriv (E := E) j (h l i) y := by
      have heq : ((c • h) l i) = fun y'' => c • h l i y'' := rfl
      rw [heq, partialDeriv_const_smul (E := E) c (h l i) (h.differentiableAt l i y),
        smul_eq_mul]
    have ec : partialDeriv (E := E) l ((c • h) i j) y =
        c * partialDeriv (E := E) l (h i j) y := by
      have heq : ((c • h) i j) = fun y'' => c • h i j y'' := rfl
      rw [heq, partialDeriv_const_smul (E := E) c (h i j) (h.differentiableAt i j y),
        smul_eq_mul]
    rw [ea, eb, ec]
    ring
  rw [Finset.sum_congr rfl (fun j _ =>
        Finset.sum_congr rfl (fun l _ => hsummand1 j l)),
    Finset.sum_congr rfl (fun j _ =>
        Finset.sum_congr rfl (fun l _ => hsummand2 j l))]
  rw [Finset.sum_congr rfl (fun j _ => (Finset.mul_sum _ _ c).symm),
    Finset.sum_congr rfl (fun j _ => (Finset.mul_sum _ _ c).symm),
    ← Finset.mul_sum, ← Finset.mul_sum]
  ring

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem chartRicciSecondOrderPrincipalSymbol_symm
    (g : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (i k : Fin (Module.finrank ℝ E)) (y : E) :
    chartRicciSecondOrderPrincipalSymbol (I := I) g α h i k y =
      chartRicciSecondOrderPrincipalSymbol (I := I) g α h k i y := by
  classical
  rw [chartRicciSecondOrderPrincipalSymbol_def, chartRicciSecondOrderPrincipalSymbol_def]
  congr 1
  have hsplit : ∀ p q : Fin (Module.finrank ℝ E),
      (∑ j : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j l y *
            (partialDeriv (E := E) j (partialDeriv (E := E) p (h l q)) y +
             partialDeriv (E := E) q (partialDeriv (E := E) l (h p j)) y -
             partialDeriv (E := E) j (partialDeriv (E := E) l (h p q)) y -
             partialDeriv (E := E) q (partialDeriv (E := E) p (h l j)) y)) =
      (∑ j : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j l y *
            partialDeriv (E := E) j (partialDeriv (E := E) p (h l q)) y) +
      (∑ j : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j l y *
            partialDeriv (E := E) q (partialDeriv (E := E) l (h p j)) y) -
      (∑ j : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j l y *
            partialDeriv (E := E) j (partialDeriv (E := E) l (h p q)) y) -
      (∑ j : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j l y *
            partialDeriv (E := E) q (partialDeriv (E := E) p (h l j)) y) := by
    intro p q
    have hinner : ∀ j : Fin (Module.finrank ℝ E),
        (∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j l y *
            (partialDeriv (E := E) j (partialDeriv (E := E) p (h l q)) y +
             partialDeriv (E := E) q (partialDeriv (E := E) l (h p j)) y -
             partialDeriv (E := E) j (partialDeriv (E := E) l (h p q)) y -
             partialDeriv (E := E) q (partialDeriv (E := E) p (h l j)) y)) =
        (∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j l y *
            partialDeriv (E := E) j (partialDeriv (E := E) p (h l q)) y) +
        (∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j l y *
            partialDeriv (E := E) q (partialDeriv (E := E) l (h p j)) y) -
        (∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j l y *
            partialDeriv (E := E) j (partialDeriv (E := E) l (h p q)) y) -
        (∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j l y *
            partialDeriv (E := E) q (partialDeriv (E := E) p (h l j)) y) := by
      intro j
      rw [show (∑ l : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g α j l y *
                (partialDeriv (E := E) j (partialDeriv (E := E) p (h l q)) y +
                 partialDeriv (E := E) q (partialDeriv (E := E) l (h p j)) y -
                 partialDeriv (E := E) j (partialDeriv (E := E) l (h p q)) y -
                 partialDeriv (E := E) q (partialDeriv (E := E) p (h l j)) y)) =
            (∑ l : Fin (Module.finrank ℝ E),
              (chartInvGramOnE (I := I) g α j l y *
                  partialDeriv (E := E) j (partialDeriv (E := E) p (h l q)) y +
                chartInvGramOnE (I := I) g α j l y *
                  partialDeriv (E := E) q (partialDeriv (E := E) l (h p j)) y -
                chartInvGramOnE (I := I) g α j l y *
                  partialDeriv (E := E) j (partialDeriv (E := E) l (h p q)) y -
                chartInvGramOnE (I := I) g α j l y *
                  partialDeriv (E := E) q (partialDeriv (E := E) p (h l j)) y)) from
        Finset.sum_congr rfl (fun l _ => by ring)]
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    rw [Finset.sum_congr rfl (fun j _ => hinner j)]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [hsplit i k, hsplit k i]
  have hA : (∑ j : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j l y *
            partialDeriv (E := E) j (partialDeriv (E := E) k (h l i)) y) =
      (∑ j : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j l y *
            partialDeriv (E := E) k (partialDeriv (E := E) l (h i j)) y) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [chartInvGramOnE_symm (I := I) g α l j y, h.symm_fun j i,
      partialDeriv_partialDeriv_perturbation_swap h i j l k y]
  have hB : (∑ j : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j l y *
            partialDeriv (E := E) i (partialDeriv (E := E) l (h k j)) y) =
      (∑ j : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j l y *
            partialDeriv (E := E) j (partialDeriv (E := E) i (h l k)) y) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [chartInvGramOnE_symm (I := I) g α l j y, h.symm_fun k l,
      partialDeriv_partialDeriv_perturbation_swap h l k i j y]
  have hC : (∑ j : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j l y *
            partialDeriv (E := E) j (partialDeriv (E := E) l (h k i)) y) =
      (∑ j : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j l y *
            partialDeriv (E := E) j (partialDeriv (E := E) l (h i k)) y) := by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [h.symm_fun k i]
  have hD : (∑ j : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j l y *
            partialDeriv (E := E) i (partialDeriv (E := E) k (h l j)) y) =
      (∑ j : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j l y *
            partialDeriv (E := E) k (partialDeriv (E := E) i (h l j)) y) := by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [partialDeriv_partialDeriv_perturbation_swap h l j i k y]
  rw [hA, hB, hC, hD]
  ring

end RicciLinearization
end DeTurck
end PDE
end DifferentialGeometry
