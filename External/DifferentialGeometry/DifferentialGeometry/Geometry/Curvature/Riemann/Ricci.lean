import DifferentialGeometry.Geometry.Curvature.Riemann.Defs
import DifferentialGeometry.Geometry.Operator.HessianTrace


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
lemma chartInvGramOnE_symm
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) (y : E) :
    chartInvGramOnE (I := I) g α i j y = chartInvGramOnE (I := I) g α j i y := by
  unfold chartInvGramOnE
  set z := (extChartAt I α).symm y
  have hG_hermit : (chartGramMatrix (I := I) g α z).IsHermitian :=
    chartGramMatrix_isHermitian (I := I) g α z
  have hGinv_hermit : (chartGramMatrix (I := I) g α z)⁻¹.IsHermitian := hG_hermit.inv
  have hentry := hGinv_hermit.apply i j
  unfold chartInvGramMatrix
  have hstar : star ((chartGramMatrix (I := I) g α z)⁻¹ j i) =
      (chartGramMatrix (I := I) g α z)⁻¹ i j := hentry
  rw [show star ((chartGramMatrix (I := I) g α z)⁻¹ j i) =
      (chartGramMatrix (I := I) g α z)⁻¹ j i from rfl] at hstar
  exact hstar.symm

omit [NeZero (Module.finrank ℝ E)] in
lemma partialDeriv_partialDeriv_chartGramOnE_swap
    (g : SmoothRiemannianMetric I M) (α : M)
    (l j a b : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    partialDeriv (E := E) a
        (partialDeriv (E := E) b (chartGramOnE (I := I) g α l j)) y =
      partialDeriv (E := E) b
        (partialDeriv (E := E) a (chartGramOnE (I := I) g α l j)) y := by
  classical
  unfold partialDeriv
  have hsmooth_target :
      ContDiffOn ℝ ∞ (chartGramOnE (I := I) g α l j) (extChartAt I α).target :=
    chartGramOnE_contDiffOn (I := I) g α l j
  have hsmooth_int :
      ContDiffOn ℝ ∞ (chartGramOnE (I := I) g α l j)
        (interior (extChartAt I α).target) :=
    hsmooth_target.mono interior_subset
  have hopen_int : IsOpen (interior (extChartAt I α).target) := isOpen_interior
  have hcontDiffAt :
      ContDiffAt ℝ ∞ (chartGramOnE (I := I) g α l j) y :=
    hsmooth_int.contDiffAt (hopen_int.mem_nhds hy)
  have hsymm_2 :
      IsSymmSndFDerivAt ℝ (chartGramOnE (I := I) g α l j) y := by
    refine ContDiffAt.isSymmSndFDerivAt hcontDiffAt ?_
    rw [minSmoothness_of_isRCLikeNormedField]
    decide
  have hg_diff :
      DifferentiableAt ℝ (fderiv ℝ (chartGramOnE (I := I) g α l j)) y := by
    have hfderiv_smooth : ContDiffOn ℝ ∞
        (fderiv ℝ (chartGramOnE (I := I) g α l j))
        (interior (extChartAt I α).target) :=
      hsmooth_int.fderiv_of_isOpen isOpen_interior (by rw [ENat.coe_top_add_one])
    have hcontDiff_at_fderiv :
        ContDiffAt ℝ ∞ (fderiv ℝ (chartGramOnE (I := I) g α l j)) y :=
      hfderiv_smooth.contDiffAt (hopen_int.mem_nhds hy)
    exact hcontDiff_at_fderiv.differentiableAt (by simp)
  have hkey : ∀ p q : Fin (Module.finrank ℝ E),
      fderiv ℝ
          (fun z =>
            fderiv ℝ (chartGramOnE (I := I) g α l j) z ((chartModelBasis E) q))
          y ((chartModelBasis E) p) =
        (fderiv ℝ (fderiv ℝ (chartGramOnE (I := I) g α l j)) y
          ((chartModelBasis E) p)) ((chartModelBasis E) q) := by
    intro p q
    set L : (E →L[ℝ] ℝ) →L[ℝ] ℝ :=
      ContinuousLinearMap.apply ℝ ℝ ((chartModelBasis E) q)
    have hcomp_eq : (fun z : E =>
          fderiv ℝ (chartGramOnE (I := I) g α l j) z ((chartModelBasis E) q)) =
        L ∘ (fderiv ℝ (chartGramOnE (I := I) g α l j)) := by
      funext z; rfl
    rw [hcomp_eq, fderiv_comp y L.differentiableAt hg_diff]
    rw [L.fderiv]
    rfl
  rw [hkey a b, hkey b a]
  exact hsymm_2 _ _

omit [NeZero (Module.finrank ℝ E)] in
private lemma sum_invGram_partialDeriv_swap
    (g : SmoothRiemannianMetric I M) (α : M)
    (i : Fin (Module.finrank ℝ E)) (y : E) :
    (∑ j : Fin (Module.finrank ℝ E),
      ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g α j l y *
          partialDeriv (E := E) j (chartGramOnE (I := I) g α l i) y) =
    (∑ j : Fin (Module.finrank ℝ E),
      ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g α j l y *
          partialDeriv (E := E) l (chartGramOnE (I := I) g α i j) y) := by
  classical
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro j _
  refine Finset.sum_congr rfl ?_
  intro l _
  rw [chartInvGramOnE_symm (I := I) g α l j y]
  congr 1
  exact congrArg (fun f => partialDeriv (E := E) l f y)
    (funext (fun y' => chartGramOnE_symm (I := I) g α j i y'))

omit [NeZero (Module.finrank ℝ E)] in
lemma chartContractedChristoffel_eq_half_invGram_partialDeriv
    (g : SmoothRiemannianMetric I M) (α : M)
    (i : Fin (Module.finrank ℝ E)) (y : E) :
    (∑ j : Fin (Module.finrank ℝ E),
        chartChristoffel (I := I) g α i j j y) =
      (1 / 2 : ℝ) *
        ∑ j : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j l y *
            partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y := by
  classical
  have hexp : (∑ j : Fin (Module.finrank ℝ E),
        chartChristoffel (I := I) g α i j j y) =
      (∑ j : Fin (Module.finrank ℝ E),
        (1 / 2 : ℝ) *
          ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α j l y *
              (partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y +
               partialDeriv (E := E) j (chartGramOnE (I := I) g α l i) y -
               partialDeriv (E := E) l (chartGramOnE (I := I) g α i j) y)) := rfl
  rw [hexp]
  rw [← Finset.mul_sum]
  congr 1
  have hexpand : ∀ j l : Fin (Module.finrank ℝ E),
      chartInvGramOnE (I := I) g α j l y *
        (partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y +
         partialDeriv (E := E) j (chartGramOnE (I := I) g α l i) y -
         partialDeriv (E := E) l (chartGramOnE (I := I) g α i j) y) =
      chartInvGramOnE (I := I) g α j l y *
        partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y +
        chartInvGramOnE (I := I) g α j l y *
          partialDeriv (E := E) j (chartGramOnE (I := I) g α l i) y -
        chartInvGramOnE (I := I) g α j l y *
          partialDeriv (E := E) l (chartGramOnE (I := I) g α i j) y := fun j l => by ring
  have hdouble :
      (∑ j : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j l y *
            (partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y +
             partialDeriv (E := E) j (chartGramOnE (I := I) g α l i) y -
             partialDeriv (E := E) l (chartGramOnE (I := I) g α i j) y)) =
      (∑ j : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j l y *
            partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y) +
      (∑ j : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j l y *
            partialDeriv (E := E) j (chartGramOnE (I := I) g α l i) y) -
      (∑ j : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j l y *
            partialDeriv (E := E) l (chartGramOnE (I := I) g α i j) y) := by
    have hinner : ∀ j : Fin (Module.finrank ℝ E),
        (∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j l y *
            (partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y +
             partialDeriv (E := E) j (chartGramOnE (I := I) g α l i) y -
             partialDeriv (E := E) l (chartGramOnE (I := I) g α i j) y)) =
        (∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j l y *
            partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y) +
        (∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j l y *
            partialDeriv (E := E) j (chartGramOnE (I := I) g α l i) y) -
        (∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j l y *
            partialDeriv (E := E) l (chartGramOnE (I := I) g α i j) y) := by
      intro j
      rw [show (∑ l : Fin (Module.finrank ℝ E),
                chartInvGramOnE (I := I) g α j l y *
                  (partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y +
                   partialDeriv (E := E) j (chartGramOnE (I := I) g α l i) y -
                   partialDeriv (E := E) l (chartGramOnE (I := I) g α i j) y)) =
              (∑ l : Fin (Module.finrank ℝ E),
                (chartInvGramOnE (I := I) g α j l y *
                  partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y +
                chartInvGramOnE (I := I) g α j l y *
                  partialDeriv (E := E) j (chartGramOnE (I := I) g α l i) y -
                chartInvGramOnE (I := I) g α j l y *
                  partialDeriv (E := E) l (chartGramOnE (I := I) g α i j) y)) from
        Finset.sum_congr rfl (fun l _ => hexpand j l)]
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    rw [Finset.sum_congr rfl (fun j _ => hinner j)]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [hdouble]
  rw [sum_invGram_partialDeriv_swap (I := I) g α i y]
  ring

omit [NeZero (Module.finrank ℝ E)] in
private lemma partialDeriv_chartGramOnE_contDiffOn_interior
    (g : SmoothRiemannianMetric I M) (α : M)
    (l j b : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (partialDeriv (E := E) b (chartGramOnE (I := I) g α l j))
      (interior (extChartAt I α).target) := by
  classical
  have hf_target : ContDiffOn ℝ ∞ (chartGramOnE (I := I) g α l j)
      (extChartAt I α).target := chartGramOnE_contDiffOn (I := I) g α l j
  have hf_int : ContDiffOn ℝ ∞ (chartGramOnE (I := I) g α l j)
      (interior (extChartAt I α).target) := hf_target.mono interior_subset
  have hfderiv : ContDiffOn ℝ ∞ (fderiv ℝ (chartGramOnE (I := I) g α l j))
      (interior (extChartAt I α).target) :=
    hf_int.fderiv_of_isOpen isOpen_interior (by rw [ENat.coe_top_add_one])
  unfold partialDeriv
  exact hfderiv.clm_apply contDiffOn_const

omit [NeZero (Module.finrank ℝ E)] in
private lemma chartInvGramOnE_diffAt_int
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
private lemma partialDeriv_chartGramOnE_diffAt_int
    (g : SmoothRiemannianMetric I M) (α : M)
    (l j b : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    DifferentiableAt ℝ
      (partialDeriv (E := E) b (chartGramOnE (I := I) g α l j)) y := by
  have hcd : ContDiffOn ℝ ∞
      (partialDeriv (E := E) b (chartGramOnE (I := I) g α l j))
      (interior (extChartAt I α).target) :=
    partialDeriv_chartGramOnE_contDiffOn_interior (I := I) g α l j b
  have hop : IsOpen (interior (extChartAt I α).target) := isOpen_interior
  have hat : ContDiffAt ℝ ∞
      (partialDeriv (E := E) b (chartGramOnE (I := I) g α l j)) y :=
    hcd.contDiffAt (hop.mem_nhds hy)
  exact hat.differentiableAt (by simp)

omit [NeZero (Module.finrank ℝ E)] in
private lemma chartChristoffel_diag_contDiffOn_interior
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (fun y : E => chartChristoffel (I := I) g α i j j y)
      (interior (extChartAt I α).target) := by
  classical
  have heq : (fun y : E => chartChristoffel (I := I) g α i j j y) =
      (fun y : E => (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g α j l y *
          (partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y +
           partialDeriv (E := E) j (chartGramOnE (I := I) g α l i) y -
           partialDeriv (E := E) l (chartGramOnE (I := I) g α i j) y)) := rfl
  rw [heq]
  refine ContDiffOn.mul contDiffOn_const ?_
  refine ContDiffOn.sum (fun l _ => ?_)
  refine ContDiffOn.mul ?_ ?_
  · exact (chartInvGramOnE_contDiffOn (I := I) g α j l).mono interior_subset
  · refine ContDiffOn.sub (ContDiffOn.add ?_ ?_) ?_
    · exact partialDeriv_chartGramOnE_contDiffOn_interior (I := I) g α l j i
    · exact partialDeriv_chartGramOnE_contDiffOn_interior (I := I) g α l i j
    · exact partialDeriv_chartGramOnE_contDiffOn_interior (I := I) g α i j l

omit [NeZero (Module.finrank ℝ E)] in
private lemma chartChristoffel_diag_diffAt_int
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    DifferentiableAt ℝ
      (fun y' : E => chartChristoffel (I := I) g α i j j y') y := by
  have hcd : ContDiffOn ℝ ∞
      (fun y' : E => chartChristoffel (I := I) g α i j j y')
      (interior (extChartAt I α).target) :=
    chartChristoffel_diag_contDiffOn_interior (I := I) g α i j
  have hop : IsOpen (interior (extChartAt I α).target) := isOpen_interior
  have hat : ContDiffAt ℝ ∞
      (fun y' : E => chartChristoffel (I := I) g α i j j y') y :=
    hcd.contDiffAt (hop.mem_nhds hy)
  exact hat.differentiableAt (by simp)

omit [NeZero (Module.finrank ℝ E)] in
private lemma traceCyclic_invGram_partial
    (g : SmoothRiemannianMetric I M) (α : M)
    (i k : Fin (Module.finrank ℝ E)) (y : E) :
    (∑ j : Fin (Module.finrank ℝ E),
      ∑ l : Fin (Module.finrank ℝ E),
      ∑ a : Fin (Module.finrank ℝ E),
      ∑ b : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g α j a y *
          chartInvGramOnE (I := I) g α b l y *
            partialDeriv (E := E) k (chartGramOnE (I := I) g α a b) y *
              partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y) =
    (∑ j : Fin (Module.finrank ℝ E),
      ∑ l : Fin (Module.finrank ℝ E),
      ∑ a : Fin (Module.finrank ℝ E),
      ∑ b : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g α j a y *
          chartInvGramOnE (I := I) g α b l y *
            partialDeriv (E := E) i (chartGramOnE (I := I) g α a b) y *
              partialDeriv (E := E) k (chartGramOnE (I := I) g α l j) y) := by
  classical
  set H : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    Matrix.of fun a b => chartInvGramOnE (I := I) g α a b y with hH_def
  set Ak : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    Matrix.of fun a b =>
      partialDeriv (E := E) k (chartGramOnE (I := I) g α a b) y with hAk_def
  set Ai : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    Matrix.of fun a b =>
      partialDeriv (E := E) i (chartGramOnE (I := I) g α a b) y with hAi_def
  have hLHS_eq_trace :
      (∑ j : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
        ∑ a : Fin (Module.finrank ℝ E),
        ∑ b : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j a y *
            chartInvGramOnE (I := I) g α b l y *
              partialDeriv (E := E) k (chartGramOnE (I := I) g α a b) y *
                partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y) =
      (H * Ak * H * Ai).trace := by
    have hexpand_diag : ∀ j : Fin (Module.finrank ℝ E),
        (H * Ak * H * Ai) j j =
          ∑ l : Fin (Module.finrank ℝ E),
          ∑ a : Fin (Module.finrank ℝ E),
          ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α j a y *
              chartInvGramOnE (I := I) g α b l y *
                partialDeriv (E := E) k (chartGramOnE (I := I) g α a b) y *
                  partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y := by
      intro j
      simp only [Matrix.mul_apply, hH_def, hAk_def, hAi_def, Matrix.of_apply,
        Finset.sum_mul]
      refine Finset.sum_congr rfl ?_
      intro l _
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_
      intro a _
      refine Finset.sum_congr rfl ?_
      intro b _
      ring
    rw [Matrix.trace]
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [Matrix.diag_apply]
    rw [hexpand_diag j]
  have hRHS_eq_trace :
      (∑ j : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
        ∑ a : Fin (Module.finrank ℝ E),
        ∑ b : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j a y *
            chartInvGramOnE (I := I) g α b l y *
              partialDeriv (E := E) i (chartGramOnE (I := I) g α a b) y *
                partialDeriv (E := E) k (chartGramOnE (I := I) g α l j) y) =
      (H * Ai * H * Ak).trace := by
    have hexpand_diag : ∀ j : Fin (Module.finrank ℝ E),
        (H * Ai * H * Ak) j j =
          ∑ l : Fin (Module.finrank ℝ E),
          ∑ a : Fin (Module.finrank ℝ E),
          ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α j a y *
              chartInvGramOnE (I := I) g α b l y *
                partialDeriv (E := E) i (chartGramOnE (I := I) g α a b) y *
                  partialDeriv (E := E) k (chartGramOnE (I := I) g α l j) y := by
      intro j
      simp only [Matrix.mul_apply, hH_def, hAi_def, hAk_def, Matrix.of_apply,
        Finset.sum_mul]
      refine Finset.sum_congr rfl ?_
      intro l _
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_
      intro a _
      refine Finset.sum_congr rfl ?_
      intro b _
      ring
    rw [Matrix.trace]
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [Matrix.diag_apply]
    rw [hexpand_diag j]
  rw [hLHS_eq_trace, hRHS_eq_trace]
  have heq1 : (H * Ak * H * Ai).trace = ((H * Ak) * (H * Ai)).trace := by
    rw [Matrix.mul_assoc]
  have heq2 : ((H * Ai) * (H * Ak)).trace = (H * Ai * H * Ak).trace := by
    rw [← Matrix.mul_assoc]
  rw [heq1, Matrix.trace_mul_comm (H * Ak) (H * Ai), heq2]

omit [NeZero (Module.finrank ℝ E)] in
private lemma partialDeriv_doubleSum_invGram_partialGram
    (g : SmoothRiemannianMetric I M) (α : M)
    (i k : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    partialDeriv (E := E) k
        (fun y' : E => ∑ j : Fin (Module.finrank ℝ E),
          ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α j l y' *
              partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y') y =
      ∑ j : Fin (Module.finrank ℝ E),
      ∑ l : Fin (Module.finrank ℝ E),
        (partialDeriv (E := E) k (chartInvGramOnE (I := I) g α j l) y *
            partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y +
          chartInvGramOnE (I := I) g α j l y *
            partialDeriv (E := E) k
              (partialDeriv (E := E) i (chartGramOnE (I := I) g α l j)) y) := by
  classical
  have hdiff_innermost : ∀ j l : Fin (Module.finrank ℝ E),
      DifferentiableAt ℝ
        (fun y' : E => chartInvGramOnE (I := I) g α j l y' *
          partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y') y := by
    intro j l
    refine DifferentiableAt.mul ?_ ?_
    · exact chartInvGramOnE_diffAt_int (I := I) g α j l hy
    · exact partialDeriv_chartGramOnE_diffAt_int (I := I) g α l j i hy
  have hdiff_inner : ∀ j : Fin (Module.finrank ℝ E),
      DifferentiableAt ℝ
        (fun y' : E => ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j l y' *
            partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y') y := by
    intro j
    exact DifferentiableAt.fun_sum (fun l _ => hdiff_innermost j l)
  have hsum_outer : partialDeriv (E := E) k
        (fun y' : E => ∑ j : Fin (Module.finrank ℝ E),
          ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α j l y' *
              partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y') y =
      ∑ j : Fin (Module.finrank ℝ E),
        partialDeriv (E := E) k
          (fun y' : E => ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α j l y' *
              partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y') y := by
    change fderiv ℝ
        (fun y' : E => ∑ j : Fin (Module.finrank ℝ E),
          ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α j l y' *
              partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y') y
        ((chartModelBasis E) k) =
      ∑ j : Fin (Module.finrank ℝ E),
        fderiv ℝ
          (fun y' : E => ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α j l y' *
              partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y') y
          ((chartModelBasis E) k)
    rw [fderiv_fun_sum (fun j _ => hdiff_inner j)]
    rw [ContinuousLinearMap.coe_sum', Finset.sum_apply]
  rw [hsum_outer]
  refine Finset.sum_congr rfl ?_
  intro j _
  have hsum_inner : partialDeriv (E := E) k
        (fun y' : E => ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j l y' *
            partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y') y =
      ∑ l : Fin (Module.finrank ℝ E),
        partialDeriv (E := E) k
          (fun y' : E => chartInvGramOnE (I := I) g α j l y' *
            partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y') y := by
    change fderiv ℝ
        (fun y' : E => ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j l y' *
            partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y') y
        ((chartModelBasis E) k) =
      ∑ l : Fin (Module.finrank ℝ E),
        fderiv ℝ
          (fun y' : E => chartInvGramOnE (I := I) g α j l y' *
            partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y') y
          ((chartModelBasis E) k)
    rw [fderiv_fun_sum (fun l _ => hdiff_innermost j l)]
    rw [ContinuousLinearMap.coe_sum', Finset.sum_apply]
  rw [hsum_inner]
  refine Finset.sum_congr rfl ?_
  intro l _
  have hu : DifferentiableAt ℝ (chartInvGramOnE (I := I) g α j l) y :=
    chartInvGramOnE_diffAt_int (I := I) g α j l hy
  have hv : DifferentiableAt ℝ
      (partialDeriv (E := E) i (chartGramOnE (I := I) g α l j)) y :=
    partialDeriv_chartGramOnE_diffAt_int (I := I) g α l j i hy
  change fderiv ℝ
      (fun y' : E => chartInvGramOnE (I := I) g α j l y' *
        partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y') y
      ((chartModelBasis E) k) =
    partialDeriv (E := E) k (chartInvGramOnE (I := I) g α j l) y *
        partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y +
      chartInvGramOnE (I := I) g α j l y *
        partialDeriv (E := E) k
          (partialDeriv (E := E) i (chartGramOnE (I := I) g α l j)) y
  rw [fderiv_fun_mul (𝕜 := ℝ) hu hv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul]
  change chartInvGramOnE (I := I) g α j l y *
      (partialDeriv (E := E) k
        (partialDeriv (E := E) i (chartGramOnE (I := I) g α l j)) y) +
      partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y *
        (partialDeriv (E := E) k (chartInvGramOnE (I := I) g α j l) y) =
    partialDeriv (E := E) k (chartInvGramOnE (I := I) g α j l) y *
        partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y +
      chartInvGramOnE (I := I) g α j l y *
        partialDeriv (E := E) k
          (partialDeriv (E := E) i (chartGramOnE (I := I) g α l j)) y
  ring

omit [NeZero (Module.finrank ℝ E)] in
theorem partialDeriv_contractedChristoffel_swap
    (g : SmoothRiemannianMetric I M) (α : M)
    (i k : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    partialDeriv (E := E) k
        (fun y' : E => ∑ j : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g α i j j y') y =
      partialDeriv (E := E) i
        (fun y' : E => ∑ j : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g α k j j y') y := by
  classical
  have hC_i : (fun y' : E => ∑ j : Fin (Module.finrank ℝ E),
        chartChristoffel (I := I) g α i j j y') =
      (fun y' : E =>
        (1 / 2 : ℝ) *
          ∑ j : Fin (Module.finrank ℝ E),
          ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α j l y' *
              partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y') := by
    funext y'
    exact chartContractedChristoffel_eq_half_invGram_partialDeriv (I := I) g α i y'
  have hC_k : (fun y' : E => ∑ j : Fin (Module.finrank ℝ E),
        chartChristoffel (I := I) g α k j j y') =
      (fun y' : E =>
        (1 / 2 : ℝ) *
          ∑ j : Fin (Module.finrank ℝ E),
          ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α j l y' *
              partialDeriv (E := E) k (chartGramOnE (I := I) g α l j) y') := by
    funext y'
    exact chartContractedChristoffel_eq_half_invGram_partialDeriv (I := I) g α k y'
  rw [hC_i, hC_k]
  have hsmul : ∀ (μ ν : Fin (Module.finrank ℝ E)),
      partialDeriv (E := E) μ
        (fun y' : E =>
          (1 / 2 : ℝ) *
            ∑ j : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g α j l y' *
                partialDeriv (E := E) ν (chartGramOnE (I := I) g α l j) y') y =
        (1 / 2 : ℝ) *
          partialDeriv (E := E) μ
            (fun y' : E => ∑ j : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
                chartInvGramOnE (I := I) g α j l y' *
                  partialDeriv (E := E) ν (chartGramOnE (I := I) g α l j) y') y := by
    intro μ ν
    have hdiff : DifferentiableAt ℝ
        (fun y' : E => ∑ j : Fin (Module.finrank ℝ E),
          ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α j l y' *
              partialDeriv (E := E) ν (chartGramOnE (I := I) g α l j) y') y := by
      refine DifferentiableAt.fun_sum (fun j _ => ?_)
      refine DifferentiableAt.fun_sum (fun l _ => ?_)
      refine DifferentiableAt.mul ?_ ?_
      · exact chartInvGramOnE_diffAt_int (I := I) g α j l hy
      · exact partialDeriv_chartGramOnE_diffAt_int (I := I) g α l j ν hy
    change fderiv ℝ
        (fun y' : E =>
          (1 / 2 : ℝ) *
            ∑ j : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g α j l y' *
                partialDeriv (E := E) ν (chartGramOnE (I := I) g α l j) y') y
        ((chartModelBasis E) μ) =
      (1 / 2 : ℝ) *
        fderiv ℝ
          (fun y' : E => ∑ j : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g α j l y' *
                partialDeriv (E := E) ν (chartGramOnE (I := I) g α l j) y') y
          ((chartModelBasis E) μ)
    set F : E → ℝ := fun y' : E => ∑ j : Fin (Module.finrank ℝ E),
          ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α j l y' *
              partialDeriv (E := E) ν (chartGramOnE (I := I) g α l j) y' with hF_def
    have hfn_eq : (fun y' : E => (1 / 2 : ℝ) * F y') = (1 / 2 : ℝ) • F := by
      funext y'; rw [Pi.smul_apply, smul_eq_mul]
    change fderiv ℝ (fun y' : E => (1 / 2 : ℝ) * F y') y
        ((chartModelBasis E) μ) =
      (1 / 2 : ℝ) * fderiv ℝ F y ((chartModelBasis E) μ)
    rw [hfn_eq]
    rw [fderiv_const_smul hdiff]
    simp [smul_eq_mul]
  rw [hsmul k i, hsmul i k]
  congr 1
  rw [partialDeriv_doubleSum_invGram_partialGram (I := I) g α i k hy,
      partialDeriv_doubleSum_invGram_partialGram (I := I) g α k i hy]
  have hsplit_LHS :
      (∑ j : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          (partialDeriv (E := E) k (chartInvGramOnE (I := I) g α j l) y *
              partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y +
            chartInvGramOnE (I := I) g α j l y *
              partialDeriv (E := E) k
                (partialDeriv (E := E) i (chartGramOnE (I := I) g α l j)) y)) =
      (∑ j : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          partialDeriv (E := E) k (chartInvGramOnE (I := I) g α j l) y *
            partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y) +
      (∑ j : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j l y *
            partialDeriv (E := E) k
              (partialDeriv (E := E) i (chartGramOnE (I := I) g α l j)) y) := by
    have hinner : ∀ j : Fin (Module.finrank ℝ E),
        (∑ l : Fin (Module.finrank ℝ E),
          (partialDeriv (E := E) k (chartInvGramOnE (I := I) g α j l) y *
              partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y +
            chartInvGramOnE (I := I) g α j l y *
              partialDeriv (E := E) k
                (partialDeriv (E := E) i (chartGramOnE (I := I) g α l j)) y)) =
        (∑ l : Fin (Module.finrank ℝ E),
          partialDeriv (E := E) k (chartInvGramOnE (I := I) g α j l) y *
            partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y) +
        (∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j l y *
            partialDeriv (E := E) k
              (partialDeriv (E := E) i (chartGramOnE (I := I) g α l j)) y) := by
      intro j
      exact Finset.sum_add_distrib
    rw [Finset.sum_congr rfl (fun j _ => hinner j)]
    exact Finset.sum_add_distrib
  have hsplit_RHS :
      (∑ j : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          (partialDeriv (E := E) i (chartInvGramOnE (I := I) g α j l) y *
              partialDeriv (E := E) k (chartGramOnE (I := I) g α l j) y +
            chartInvGramOnE (I := I) g α j l y *
              partialDeriv (E := E) i
                (partialDeriv (E := E) k (chartGramOnE (I := I) g α l j)) y)) =
      (∑ j : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          partialDeriv (E := E) i (chartInvGramOnE (I := I) g α j l) y *
            partialDeriv (E := E) k (chartGramOnE (I := I) g α l j) y) +
      (∑ j : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j l y *
            partialDeriv (E := E) i
              (partialDeriv (E := E) k (chartGramOnE (I := I) g α l j)) y) := by
    have hinner : ∀ j : Fin (Module.finrank ℝ E),
        (∑ l : Fin (Module.finrank ℝ E),
          (partialDeriv (E := E) i (chartInvGramOnE (I := I) g α j l) y *
              partialDeriv (E := E) k (chartGramOnE (I := I) g α l j) y +
            chartInvGramOnE (I := I) g α j l y *
              partialDeriv (E := E) i
                (partialDeriv (E := E) k (chartGramOnE (I := I) g α l j)) y)) =
        (∑ l : Fin (Module.finrank ℝ E),
          partialDeriv (E := E) i (chartInvGramOnE (I := I) g α j l) y *
            partialDeriv (E := E) k (chartGramOnE (I := I) g α l j) y) +
        (∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j l y *
            partialDeriv (E := E) i
              (partialDeriv (E := E) k (chartGramOnE (I := I) g α l j)) y) := by
      intro j
      exact Finset.sum_add_distrib
    rw [Finset.sum_congr rfl (fun j _ => hinner j)]
    exact Finset.sum_add_distrib
  rw [hsplit_LHS, hsplit_RHS]
  have hSchwarz : (∑ j : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j l y *
            partialDeriv (E := E) k
              (partialDeriv (E := E) i (chartGramOnE (I := I) g α l j)) y) =
      (∑ j : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j l y *
            partialDeriv (E := E) i
              (partialDeriv (E := E) k (chartGramOnE (I := I) g α l j)) y) := by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [partialDeriv_partialDeriv_chartGramOnE_swap (I := I) g α l j k i hy]
  have hsubst_LHS :
      (∑ j : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          partialDeriv (E := E) k (chartInvGramOnE (I := I) g α j l) y *
            partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y) =
      -(∑ j : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
        ∑ a : Fin (Module.finrank ℝ E),
        ∑ b : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j a y *
            chartInvGramOnE (I := I) g α b l y *
              partialDeriv (E := E) k (chartGramOnE (I := I) g α a b) y *
                partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y) := by
    have hentry : ∀ j l : Fin (Module.finrank ℝ E),
        partialDeriv (E := E) k (chartInvGramOnE (I := I) g α j l) y *
          partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y =
        -(∑ a : Fin (Module.finrank ℝ E),
          ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α j a y *
              chartInvGramOnE (I := I) g α b l y *
                partialDeriv (E := E) k (chartGramOnE (I := I) g α a b) y *
                  partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y) := by
      intro j l
      rw [partialDeriv_chartInvGramOnE_eq (I := I) g α y k j l hy]
      rw [neg_mul]
      congr 1
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [Finset.sum_mul]
    rw [Finset.sum_congr rfl (fun j _ =>
      Finset.sum_congr rfl (fun l _ => hentry j l))]
    rw [show (∑ j : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
                -(∑ a : Fin (Module.finrank ℝ E),
                  ∑ b : Fin (Module.finrank ℝ E),
                    chartInvGramOnE (I := I) g α j a y *
                      chartInvGramOnE (I := I) g α b l y *
                        partialDeriv (E := E) k (chartGramOnE (I := I) g α a b) y *
                          partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y)) =
            -(∑ j : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
              ∑ a : Fin (Module.finrank ℝ E),
              ∑ b : Fin (Module.finrank ℝ E),
                chartInvGramOnE (I := I) g α j a y *
                  chartInvGramOnE (I := I) g α b l y *
                    partialDeriv (E := E) k (chartGramOnE (I := I) g α a b) y *
                      partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y) by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [← Finset.sum_neg_distrib]]
  have hsubst_RHS :
      (∑ j : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          partialDeriv (E := E) i (chartInvGramOnE (I := I) g α j l) y *
            partialDeriv (E := E) k (chartGramOnE (I := I) g α l j) y) =
      -(∑ j : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
        ∑ a : Fin (Module.finrank ℝ E),
        ∑ b : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α j a y *
            chartInvGramOnE (I := I) g α b l y *
              partialDeriv (E := E) i (chartGramOnE (I := I) g α a b) y *
                partialDeriv (E := E) k (chartGramOnE (I := I) g α l j) y) := by
    have hentry : ∀ j l : Fin (Module.finrank ℝ E),
        partialDeriv (E := E) i (chartInvGramOnE (I := I) g α j l) y *
          partialDeriv (E := E) k (chartGramOnE (I := I) g α l j) y =
        -(∑ a : Fin (Module.finrank ℝ E),
          ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α j a y *
              chartInvGramOnE (I := I) g α b l y *
                partialDeriv (E := E) i (chartGramOnE (I := I) g α a b) y *
                  partialDeriv (E := E) k (chartGramOnE (I := I) g α l j) y) := by
      intro j l
      rw [partialDeriv_chartInvGramOnE_eq (I := I) g α y i j l hy]
      rw [neg_mul]
      congr 1
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [Finset.sum_mul]
    rw [Finset.sum_congr rfl (fun j _ =>
      Finset.sum_congr rfl (fun l _ => hentry j l))]
    rw [show (∑ j : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
                -(∑ a : Fin (Module.finrank ℝ E),
                  ∑ b : Fin (Module.finrank ℝ E),
                    chartInvGramOnE (I := I) g α j a y *
                      chartInvGramOnE (I := I) g α b l y *
                        partialDeriv (E := E) i (chartGramOnE (I := I) g α a b) y *
                          partialDeriv (E := E) k (chartGramOnE (I := I) g α l j) y)) =
            -(∑ j : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
              ∑ a : Fin (Module.finrank ℝ E),
              ∑ b : Fin (Module.finrank ℝ E),
                chartInvGramOnE (I := I) g α j a y *
                  chartInvGramOnE (I := I) g α b l y *
                    partialDeriv (E := E) i (chartGramOnE (I := I) g α a b) y *
                      partialDeriv (E := E) k (chartGramOnE (I := I) g α l j) y) by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [← Finset.sum_neg_distrib]]
  rw [hsubst_LHS, hsubst_RHS, hSchwarz]
  rw [traceCyclic_invGram_partial (I := I) g α i k y]

omit [NeZero (Module.finrank ℝ E)] in
lemma sum_partialDeriv_eq_partialDeriv_sum_christ
    (g : SmoothRiemannianMetric I M) (α : M)
    (i k : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    (∑ j : Fin (Module.finrank ℝ E),
        partialDeriv (E := E) k (chartChristoffel (I := I) g α i j j) y) =
      partialDeriv (E := E) k
        (fun y' : E => ∑ j : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g α i j j y') y := by
  classical
  unfold partialDeriv
  have hdiff_each : ∀ j : Fin (Module.finrank ℝ E),
      DifferentiableAt ℝ
        (fun y' : E => chartChristoffel (I := I) g α i j j y') y :=
    fun j => chartChristoffel_diag_diffAt_int (I := I) g α i j hy
  rw [fderiv_fun_sum (fun j _ => hdiff_each j)]
  rw [ContinuousLinearMap.coe_sum', Finset.sum_apply]

omit [NeZero (Module.finrank ℝ E)] in
theorem chartRicciTensor_symm
    (g : SmoothRiemannianMetric I M) (α : M)
    (i k : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    chartRicciTensor (I := I) g α i k y =
      chartRicciTensor (I := I) g α k i y := by
  classical
  rw [chartRicciTensor_def, chartRicciTensor_def]
  have hLHS_replace :
      (∑ j : Fin (Module.finrank ℝ E), chartRiemannTensor (I := I) g α i j k j y) =
      (∑ j : Fin (Module.finrank ℝ E),
        (partialDeriv (E := E) j (chartChristoffel (I := I) g α i k j) y -
          partialDeriv (E := E) k (chartChristoffel (I := I) g α i j j) y +
          ∑ m : Fin (Module.finrank ℝ E),
            (chartChristoffel (I := I) g α j m j y *
                chartChristoffel (I := I) g α i k m y -
              chartChristoffel (I := I) g α k m j y *
                chartChristoffel (I := I) g α i j m y))) := by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rfl
  have hRHS_replace :
      (∑ j : Fin (Module.finrank ℝ E), chartRiemannTensor (I := I) g α k j i j y) =
      (∑ j : Fin (Module.finrank ℝ E),
        (partialDeriv (E := E) j (chartChristoffel (I := I) g α k i j) y -
          partialDeriv (E := E) i (chartChristoffel (I := I) g α k j j) y +
          ∑ m : Fin (Module.finrank ℝ E),
            (chartChristoffel (I := I) g α j m j y *
                chartChristoffel (I := I) g α k i m y -
              chartChristoffel (I := I) g α i m j y *
                chartChristoffel (I := I) g α k j m y))) := by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rfl
  rw [hLHS_replace, hRHS_replace]
  have hmsplit_L : ∀ j : Fin (Module.finrank ℝ E),
      (∑ m : Fin (Module.finrank ℝ E),
        (chartChristoffel (I := I) g α j m j y *
            chartChristoffel (I := I) g α i k m y -
          chartChristoffel (I := I) g α k m j y *
            chartChristoffel (I := I) g α i j m y)) =
      (∑ m : Fin (Module.finrank ℝ E),
        chartChristoffel (I := I) g α j m j y *
          chartChristoffel (I := I) g α i k m y) -
      (∑ m : Fin (Module.finrank ℝ E),
        chartChristoffel (I := I) g α k m j y *
          chartChristoffel (I := I) g α i j m y) := by
    intro j
    simp only [Finset.sum_sub_distrib]
  have hmsplit_R : ∀ j : Fin (Module.finrank ℝ E),
      (∑ m : Fin (Module.finrank ℝ E),
        (chartChristoffel (I := I) g α j m j y *
            chartChristoffel (I := I) g α k i m y -
          chartChristoffel (I := I) g α i m j y *
            chartChristoffel (I := I) g α k j m y)) =
      (∑ m : Fin (Module.finrank ℝ E),
        chartChristoffel (I := I) g α j m j y *
          chartChristoffel (I := I) g α k i m y) -
      (∑ m : Fin (Module.finrank ℝ E),
        chartChristoffel (I := I) g α i m j y *
          chartChristoffel (I := I) g α k j m y) := by
    intro j
    simp only [Finset.sum_sub_distrib]
  have hLHS_step : (∑ j : Fin (Module.finrank ℝ E),
        (partialDeriv (E := E) j (chartChristoffel (I := I) g α i k j) y -
          partialDeriv (E := E) k (chartChristoffel (I := I) g α i j j) y +
          ∑ m : Fin (Module.finrank ℝ E),
            (chartChristoffel (I := I) g α j m j y *
                chartChristoffel (I := I) g α i k m y -
              chartChristoffel (I := I) g α k m j y *
                chartChristoffel (I := I) g α i j m y))) =
      (∑ j : Fin (Module.finrank ℝ E),
        (partialDeriv (E := E) j (chartChristoffel (I := I) g α i k j) y -
          partialDeriv (E := E) k (chartChristoffel (I := I) g α i j j) y +
          ((∑ m : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) g α j m j y *
              chartChristoffel (I := I) g α i k m y) -
          (∑ m : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) g α k m j y *
              chartChristoffel (I := I) g α i j m y)))) := by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hmsplit_L j]
  have hRHS_step : (∑ j : Fin (Module.finrank ℝ E),
        (partialDeriv (E := E) j (chartChristoffel (I := I) g α k i j) y -
          partialDeriv (E := E) i (chartChristoffel (I := I) g α k j j) y +
          ∑ m : Fin (Module.finrank ℝ E),
            (chartChristoffel (I := I) g α j m j y *
                chartChristoffel (I := I) g α k i m y -
              chartChristoffel (I := I) g α i m j y *
                chartChristoffel (I := I) g α k j m y))) =
      (∑ j : Fin (Module.finrank ℝ E),
        (partialDeriv (E := E) j (chartChristoffel (I := I) g α k i j) y -
          partialDeriv (E := E) i (chartChristoffel (I := I) g α k j j) y +
          ((∑ m : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) g α j m j y *
              chartChristoffel (I := I) g α k i m y) -
          (∑ m : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) g α i m j y *
              chartChristoffel (I := I) g α k j m y)))) := by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hmsplit_R j]
  rw [hLHS_step, hRHS_step]
  have hLHS_redistribute :
      (∑ j : Fin (Module.finrank ℝ E),
        (partialDeriv (E := E) j (chartChristoffel (I := I) g α i k j) y -
          partialDeriv (E := E) k (chartChristoffel (I := I) g α i j j) y +
          ((∑ m : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) g α j m j y *
              chartChristoffel (I := I) g α i k m y) -
          (∑ m : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) g α k m j y *
              chartChristoffel (I := I) g α i j m y)))) =
      ((∑ j : Fin (Module.finrank ℝ E),
        partialDeriv (E := E) j (chartChristoffel (I := I) g α i k j) y) -
       (∑ j : Fin (Module.finrank ℝ E),
        partialDeriv (E := E) k (chartChristoffel (I := I) g α i j j) y) +
       (∑ j : Fin (Module.finrank ℝ E),
         ∑ m : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) g α j m j y *
              chartChristoffel (I := I) g α i k m y) -
       (∑ j : Fin (Module.finrank ℝ E),
         ∑ m : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) g α k m j y *
              chartChristoffel (I := I) g α i j m y)) := by
    have hpoint : ∀ j : Fin (Module.finrank ℝ E),
        (partialDeriv (E := E) j (chartChristoffel (I := I) g α i k j) y -
          partialDeriv (E := E) k (chartChristoffel (I := I) g α i j j) y +
          ((∑ m : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) g α j m j y *
              chartChristoffel (I := I) g α i k m y) -
          (∑ m : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) g α k m j y *
              chartChristoffel (I := I) g α i j m y))) =
        ((partialDeriv (E := E) j (chartChristoffel (I := I) g α i k j) y -
            partialDeriv (E := E) k (chartChristoffel (I := I) g α i j j) y) +
          (∑ m : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) g α j m j y *
              chartChristoffel (I := I) g α i k m y)) -
          (∑ m : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) g α k m j y *
              chartChristoffel (I := I) g α i j m y) := fun _ => by ring
    rw [Finset.sum_congr rfl (fun j _ => hpoint j)]
    rw [Finset.sum_sub_distrib]
    rw [Finset.sum_add_distrib]
    rw [Finset.sum_sub_distrib]
  have hRHS_redistribute :
      (∑ j : Fin (Module.finrank ℝ E),
        (partialDeriv (E := E) j (chartChristoffel (I := I) g α k i j) y -
          partialDeriv (E := E) i (chartChristoffel (I := I) g α k j j) y +
          ((∑ m : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) g α j m j y *
              chartChristoffel (I := I) g α k i m y) -
          (∑ m : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) g α i m j y *
              chartChristoffel (I := I) g α k j m y)))) =
      ((∑ j : Fin (Module.finrank ℝ E),
        partialDeriv (E := E) j (chartChristoffel (I := I) g α k i j) y) -
       (∑ j : Fin (Module.finrank ℝ E),
        partialDeriv (E := E) i (chartChristoffel (I := I) g α k j j) y) +
       (∑ j : Fin (Module.finrank ℝ E),
         ∑ m : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) g α j m j y *
              chartChristoffel (I := I) g α k i m y) -
       (∑ j : Fin (Module.finrank ℝ E),
         ∑ m : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) g α i m j y *
              chartChristoffel (I := I) g α k j m y)) := by
    have hpoint : ∀ j : Fin (Module.finrank ℝ E),
        (partialDeriv (E := E) j (chartChristoffel (I := I) g α k i j) y -
          partialDeriv (E := E) i (chartChristoffel (I := I) g α k j j) y +
          ((∑ m : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) g α j m j y *
              chartChristoffel (I := I) g α k i m y) -
          (∑ m : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) g α i m j y *
              chartChristoffel (I := I) g α k j m y))) =
        ((partialDeriv (E := E) j (chartChristoffel (I := I) g α k i j) y -
            partialDeriv (E := E) i (chartChristoffel (I := I) g α k j j) y) +
          (∑ m : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) g α j m j y *
              chartChristoffel (I := I) g α k i m y)) -
          (∑ m : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) g α i m j y *
              chartChristoffel (I := I) g α k j m y) := fun _ => by ring
    rw [Finset.sum_congr rfl (fun j _ => hpoint j)]
    rw [Finset.sum_sub_distrib]
    rw [Finset.sum_add_distrib]
    rw [Finset.sum_sub_distrib]
  rw [hLHS_redistribute, hRHS_redistribute]
  have hT1 : (∑ j : Fin (Module.finrank ℝ E),
        partialDeriv (E := E) j (chartChristoffel (I := I) g α i k j) y) =
      (∑ j : Fin (Module.finrank ℝ E),
        partialDeriv (E := E) j (chartChristoffel (I := I) g α k i j) y) := by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have hsym : chartChristoffel (I := I) g α i k j =
        chartChristoffel (I := I) g α k i j :=
      funext (fun y' => chartChristoffel_symm (I := I) g α i k j y')
    rw [hsym]
  have hT2 : (∑ j : Fin (Module.finrank ℝ E),
        partialDeriv (E := E) k (chartChristoffel (I := I) g α i j j) y) =
      (∑ j : Fin (Module.finrank ℝ E),
        partialDeriv (E := E) i (chartChristoffel (I := I) g α k j j) y) := by
    rw [sum_partialDeriv_eq_partialDeriv_sum_christ (I := I) g α i k hy,
        sum_partialDeriv_eq_partialDeriv_sum_christ (I := I) g α k i hy]
    exact partialDeriv_contractedChristoffel_swap (I := I) g α i k hy
  have hT3 : (∑ j : Fin (Module.finrank ℝ E),
        ∑ m : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g α j m j y *
            chartChristoffel (I := I) g α i k m y) =
      (∑ j : Fin (Module.finrank ℝ E),
        ∑ m : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g α j m j y *
            chartChristoffel (I := I) g α k i m y) := by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [chartChristoffel_symm (I := I) g α i k m]
  have hT4 : (∑ j : Fin (Module.finrank ℝ E),
        ∑ m : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g α k m j y *
            chartChristoffel (I := I) g α i j m y) =
      (∑ j : Fin (Module.finrank ℝ E),
        ∑ m : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g α i m j y *
            chartChristoffel (I := I) g α k j m y) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    refine Finset.sum_congr rfl (fun m _ => ?_)
    ring
  rw [hT1, hT2, hT3, hT4]

omit [NeZero (Module.finrank ℝ E)] in
theorem chartRicciTensor_symm_of_boundaryless [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    (i k : Fin (Module.finrank ℝ E))
    {x : M} (hx : x ∈ (chartAt H α).source) :
    chartRicciTensor (I := I) g α i k (extChartAt I α x) =
      chartRicciTensor (I := I) g α k i (extChartAt I α x) := by
  have hxsrc : x ∈ (extChartAt I α).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hx
  have hx_target : extChartAt I α x ∈ (extChartAt I α).target :=
    (extChartAt I α).map_source hxsrc
  have hx_int : extChartAt I α x ∈ interior (extChartAt I α).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) α hx_target
  exact chartRicciTensor_symm (I := I) g α i k hx_int

omit [NeZero (Module.finrank ℝ E)] in
theorem ricciFun_isPointwiseSymm_of_boundaryless [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) :
    IsPointwiseSymm (ricciFun (I := I) (M := M) g) := by
  refine ricciFun_symm_of_chartRicciTensor_symm (I := I) (M := M) g ?_
  intro x i k
  have hxsrc : x ∈ (chartAt H x).source := mem_chart_source H x
  exact chartRicciTensor_symm_of_boundaryless (I := I) g x i k hxsrc

end DivergenceTheorem
end Integral
end DifferentialGeometry
