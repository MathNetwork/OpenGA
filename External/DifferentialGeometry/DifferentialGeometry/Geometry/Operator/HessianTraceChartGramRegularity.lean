import DifferentialGeometry.Geometry.Operator.Hessian
import DifferentialGeometry.Geometry.Operator.VossWeyl
import DifferentialGeometry.Analysis.Integration.Measure.Family


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
private lemma partialDeriv_scalarOnE_contDiffOn_interior
    (α : M) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (j : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (partialDeriv (E := E) j (scalarOnE (I := I) α f))
      (interior (extChartAt I α).target) := by
  classical
  have hf_target : ContDiffOn ℝ ∞ (scalarOnE (I := I) α f) (extChartAt I α).target :=
    scalarOnE_contDiffOn (I := I) α hf
  have hf_int : ContDiffOn ℝ ∞ (scalarOnE (I := I) α f)
      (interior (extChartAt I α).target) := hf_target.mono interior_subset
  have hfderiv : ContDiffOn ℝ ∞ (fderiv ℝ (scalarOnE (I := I) α f))
      (interior (extChartAt I α).target) :=
    hf_int.fderiv_of_isOpen isOpen_interior (by rw [ENat.coe_top_add_one])
  unfold partialDeriv
  exact hfderiv.clm_apply contDiffOn_const

omit [NeZero (Module.finrank ℝ E)] in
lemma chartInvGramOnE_contDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (chartInvGramOnE (I := I) g α i j) (extChartAt I α).target := by
  classical
  have hbase : ContMDiffOn I 𝓘(ℝ) ∞
      (fun x : M => chartInvGramMatrix (I := I) g α x i j)
      (trivializationAt E (TangentSpace I) α).baseSet :=
    chartInvGramMatrix_entry_contMDiffOn (I := I) g α i j
  have hsymm : ContMDiffOn 𝓘(ℝ, E) I ∞ (extChartAt I α).symm
      (extChartAt I α).target := contMDiffOn_extChartAt_symm (I := I) α
  have hsubset : (extChartAt I α).target ⊆
      (extChartAt I α).symm ⁻¹'
        (trivializationAt E (TangentSpace I) α).baseSet := by
    intro y hy
    have hsource : (extChartAt I α).symm y ∈ (extChartAt I α).source :=
      (extChartAt I α).map_target hy
    rw [extChartAt_source_eq_chartAt_source (I := I)] at hsource
    rw [trivializationAt_baseSet_eq_chartAt_source]
    exact hsource
  have hcomp : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) ∞
      ((fun x : M => chartInvGramMatrix (I := I) g α x i j) ∘
        (extChartAt I α).symm)
      (extChartAt I α).target := hbase.comp hsymm hsubset
  exact hcomp.contDiffOn

omit [NeZero (Module.finrank ℝ E)] in
lemma gradChartCoeffOnE_contDiffOn_interior
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (i : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (gradChartCoeffOnE (I := I) g α f i)
      (interior (extChartAt I α).target) := by
  classical
  unfold gradChartCoeffOnE
  refine ContDiffOn.sum (fun j _ => ?_)
  refine ContDiffOn.mul ?_ ?_
  · exact (chartInvGramOnE_contDiffOn (I := I) g α i j).mono interior_subset
  · exact partialDeriv_scalarOnE_contDiffOn_interior (I := I) α hf j

omit [NeZero (Module.finrank ℝ E)] in
lemma partialDeriv_gradChartCoeffOnE_expand
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (i : Fin (Module.finrank ℝ E))
    {y : E} (hy : y ∈ interior (extChartAt I α).target) :
    partialDeriv (E := E) i (gradChartCoeffOnE (I := I) g α f i) y =
      ∑ j : Fin (Module.finrank ℝ E),
        (partialDeriv (E := E) i (chartInvGramOnE (I := I) g α i j) y *
            partialDeriv (E := E) j (scalarOnE (I := I) α f) y +
          chartInvGramOnE (I := I) g α i j y *
            chartIteratedPartialDeriv (I := I) α f i j y) := by
  classical
  have hop_int : IsOpen (interior (extChartAt I α).target) := isOpen_interior
  have hy_nhd : interior (extChartAt I α).target ∈ 𝓝 y := hop_int.mem_nhds hy
  have hG : ∀ j : Fin (Module.finrank ℝ E),
      DifferentiableAt ℝ (chartInvGramOnE (I := I) g α i j) y := by
    intro j
    have hcd_target : ContDiffOn ℝ ∞ (chartInvGramOnE (I := I) g α i j)
        (extChartAt I α).target := chartInvGramOnE_contDiffOn (I := I) g α i j
    have hcd_int : ContDiffOn ℝ ∞ (chartInvGramOnE (I := I) g α i j)
        (interior (extChartAt I α).target) := hcd_target.mono interior_subset
    have hcat : ContDiffAt ℝ ∞ (chartInvGramOnE (I := I) g α i j) y :=
      hcd_int.contDiffAt hy_nhd
    exact hcat.differentiableAt (by simp)
  have hF : ∀ j : Fin (Module.finrank ℝ E),
      DifferentiableAt ℝ
        (partialDeriv (E := E) j (scalarOnE (I := I) α f)) y := by
    intro j
    have hcd_int : ContDiffOn ℝ ∞
        (partialDeriv (E := E) j (scalarOnE (I := I) α f))
        (interior (extChartAt I α).target) :=
      partialDeriv_scalarOnE_contDiffOn_interior (I := I) α hf j
    have hcat : ContDiffAt ℝ ∞
        (partialDeriv (E := E) j (scalarOnE (I := I) α f)) y :=
      hcd_int.contDiffAt hy_nhd
    exact hcat.differentiableAt (by simp)
  have hprod : ∀ j : Fin (Module.finrank ℝ E),
      DifferentiableAt ℝ
        (fun y' : E => chartInvGramOnE (I := I) g α i j y' *
          partialDeriv (E := E) j (scalarOnE (I := I) α f) y') y :=
    fun j => (hG j).fun_mul (hF j)
  have hgrad_split : partialDeriv (E := E) i
        (gradChartCoeffOnE (I := I) g α f i) y =
      ∑ j : Fin (Module.finrank ℝ E),
        partialDeriv (E := E) i
          (fun y' : E => chartInvGramOnE (I := I) g α i j y' *
            partialDeriv (E := E) j (scalarOnE (I := I) α f) y') y := by
    change (fderiv ℝ (gradChartCoeffOnE (I := I) g α f i) y) ((chartModelBasis E) i) =
        ∑ j : Fin (Module.finrank ℝ E),
          partialDeriv (E := E) i
            (fun y' : E => chartInvGramOnE (I := I) g α i j y' *
              partialDeriv (E := E) j (scalarOnE (I := I) α f) y') y
    have h_eq_fn : (gradChartCoeffOnE (I := I) g α f i) =
        fun y' : E => ∑ j : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α i j y' *
            partialDeriv (E := E) j (scalarOnE (I := I) α f) y' := by
      funext y'; rfl
    rw [h_eq_fn]
    rw [fderiv_fun_sum (fun j _ => hprod j)]
    rw [ContinuousLinearMap.sum_apply]
    rfl
  rw [hgrad_split]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  change partialDeriv (E := E) i
        (fun y' : E => chartInvGramOnE (I := I) g α i j y' *
          partialDeriv (E := E) j (scalarOnE (I := I) α f) y') y =
      partialDeriv (E := E) i (chartInvGramOnE (I := I) g α i j) y *
            partialDeriv (E := E) j (scalarOnE (I := I) α f) y +
          chartInvGramOnE (I := I) g α i j y *
            chartIteratedPartialDeriv (I := I) α f i j y
  unfold partialDeriv chartIteratedPartialDeriv
  have hF_unfolded : DifferentiableAt ℝ
      (fun y' : E => fderiv ℝ (scalarOnE (I := I) α f) y' ((chartModelBasis E) j)) y :=
    hF j
  rw [fderiv_fun_mul (𝕜 := ℝ) (hG j) hF_unfolded]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul]
  change chartInvGramOnE (I := I) g α i j y *
      ((fderiv ℝ (partialDeriv (E := E) j (scalarOnE (I := I) α f)) y)
        ((chartModelBasis E) i)) +
      (fderiv ℝ (scalarOnE (I := I) α f) y) ((chartModelBasis E) j) *
        (fderiv ℝ (chartInvGramOnE (I := I) g α i j) y) ((chartModelBasis E) i) =
    (fderiv ℝ (chartInvGramOnE (I := I) g α i j) y) ((chartModelBasis E) i) *
        (fderiv ℝ (scalarOnE (I := I) α f) y) ((chartModelBasis E) j) +
      chartInvGramOnE (I := I) g α i j y *
        ((fderiv ℝ (partialDeriv (E := E) j (scalarOnE (I := I) α f)) y)
          ((chartModelBasis E) i))
  ring

omit [NeZero (Module.finrank ℝ E)] in
lemma chartGramOnE_contDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (chartGramOnE (I := I) g α i j) (extChartAt I α).target := by
  classical
  have hbase : ContMDiffOn I 𝓘(ℝ) ∞
      (fun x : M => chartGramMatrix (I := I) g α x i j)
      (trivializationAt E (TangentSpace I) α).baseSet :=
    chartGramMatrix_entry_contMDiffOn (I := I) g α i j
  have hsymm : ContMDiffOn 𝓘(ℝ, E) I ∞ (extChartAt I α).symm
      (extChartAt I α).target := contMDiffOn_extChartAt_symm (I := I) α
  have hsubset : (extChartAt I α).target ⊆
      (extChartAt I α).symm ⁻¹'
        (trivializationAt E (TangentSpace I) α).baseSet := by
    intro y hy
    have hsource : (extChartAt I α).symm y ∈ (extChartAt I α).source :=
      (extChartAt I α).map_target hy
    rw [extChartAt_source_eq_chartAt_source (I := I)] at hsource
    rw [trivializationAt_baseSet_eq_chartAt_source]
    exact hsource
  have hcomp : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) ∞
      ((fun x : M => chartGramMatrix (I := I) g α x i j) ∘
        (extChartAt I α).symm)
      (extChartAt I α).target := hbase.comp hsymm hsubset
  exact hcomp.contDiffOn

omit [NeZero (Module.finrank ℝ E)] in
lemma chartGramOnE_differentiableAt_interior
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E))
    {y : E} (hy : y ∈ interior (extChartAt I α).target) :
    DifferentiableAt ℝ (chartGramOnE (I := I) g α i j) y := by
  have hcd_target : ContDiffOn ℝ ∞ (chartGramOnE (I := I) g α i j)
      (extChartAt I α).target := chartGramOnE_contDiffOn (I := I) g α i j
  have hcd_int : ContDiffOn ℝ ∞ (chartGramOnE (I := I) g α i j)
      (interior (extChartAt I α).target) := hcd_target.mono interior_subset
  have hop_int : IsOpen (interior (extChartAt I α).target) := isOpen_interior
  have hy_nhd : interior (extChartAt I α).target ∈ 𝓝 y := hop_int.mem_nhds hy
  exact (hcd_int.contDiffAt hy_nhd).differentiableAt (by simp)

omit [NeZero (Module.finrank ℝ E)] in
theorem chartChristoffel_contDiffOn_interior
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j k : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (chartChristoffel (I := I) g α i j k)
      (interior (extChartAt I α).target) := by
  classical
  have hrewrite : (chartChristoffel (I := I) g α i j k) =
      fun y : E =>
        (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α k l y *
            (partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y +
             partialDeriv (E := E) j (chartGramOnE (I := I) g α l i) y -
             partialDeriv (E := E) l (chartGramOnE (I := I) g α i j) y) := by
    funext y
    rw [chartChristoffel_def]
    refine congrArg (fun t => (1 / 2 : ℝ) * t) ?_
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rfl
  rw [hrewrite]
  have hsum_smooth :
      ContDiffOn ℝ ∞
        (fun y : E => ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α k l y *
            (partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y +
             partialDeriv (E := E) j (chartGramOnE (I := I) g α l i) y -
             partialDeriv (E := E) l (chartGramOnE (I := I) g α i j) y))
        (interior (extChartAt I α).target) := by
    refine ContDiffOn.sum (fun l _ => ?_)
    refine ContDiffOn.mul ?_ ?_
    · exact (chartInvGramOnE_contDiffOn (I := I) g α k l).mono interior_subset
    · have hi : ContDiffOn ℝ ∞
          (partialDeriv (E := E) i (chartGramOnE (I := I) g α l j))
          (interior (extChartAt I α).target) := by
        unfold partialDeriv
        have hG : ContDiffOn ℝ ∞ (chartGramOnE (I := I) g α l j)
            (interior (extChartAt I α).target) :=
          (chartGramOnE_contDiffOn (I := I) g α l j).mono interior_subset
        have hfderiv : ContDiffOn ℝ ∞
            (fderiv ℝ (chartGramOnE (I := I) g α l j))
            (interior (extChartAt I α).target) :=
          hG.fderiv_of_isOpen isOpen_interior (by rw [ENat.coe_top_add_one])
        exact hfderiv.clm_apply contDiffOn_const
      have hj : ContDiffOn ℝ ∞
          (partialDeriv (E := E) j (chartGramOnE (I := I) g α l i))
          (interior (extChartAt I α).target) := by
        unfold partialDeriv
        have hG : ContDiffOn ℝ ∞ (chartGramOnE (I := I) g α l i)
            (interior (extChartAt I α).target) :=
          (chartGramOnE_contDiffOn (I := I) g α l i).mono interior_subset
        have hfderiv : ContDiffOn ℝ ∞
            (fderiv ℝ (chartGramOnE (I := I) g α l i))
            (interior (extChartAt I α).target) :=
          hG.fderiv_of_isOpen isOpen_interior (by rw [ENat.coe_top_add_one])
        exact hfderiv.clm_apply contDiffOn_const
      have hl : ContDiffOn ℝ ∞
          (partialDeriv (E := E) l (chartGramOnE (I := I) g α i j))
          (interior (extChartAt I α).target) := by
        unfold partialDeriv
        have hG : ContDiffOn ℝ ∞ (chartGramOnE (I := I) g α i j)
            (interior (extChartAt I α).target) :=
          (chartGramOnE_contDiffOn (I := I) g α i j).mono interior_subset
        have hfderiv : ContDiffOn ℝ ∞
            (fderiv ℝ (chartGramOnE (I := I) g α i j))
            (interior (extChartAt I α).target) :=
          hG.fderiv_of_isOpen isOpen_interior (by rw [ENat.coe_top_add_one])
        exact hfderiv.clm_apply contDiffOn_const
      exact (hi.add hj).sub hl
  exact (contDiffOn_const (c := (1 / 2 : ℝ))).mul hsum_smooth

omit [NeZero (Module.finrank ℝ E)] in
lemma chartInvGramOnE_differentiableAt_interior
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E))
    {y : E} (hy : y ∈ interior (extChartAt I α).target) :
    DifferentiableAt ℝ (chartInvGramOnE (I := I) g α i j) y := by
  have hcd_target : ContDiffOn ℝ ∞ (chartInvGramOnE (I := I) g α i j)
      (extChartAt I α).target := chartInvGramOnE_contDiffOn (I := I) g α i j
  have hcd_int : ContDiffOn ℝ ∞ (chartInvGramOnE (I := I) g α i j)
      (interior (extChartAt I α).target) := hcd_target.mono interior_subset
  have hop_int : IsOpen (interior (extChartAt I α).target) := isOpen_interior
  have hy_nhd : interior (extChartAt I α).target ∈ 𝓝 y := hop_int.mem_nhds hy
  exact (hcd_int.contDiffAt hy_nhd).differentiableAt (by simp)

omit [NeZero (Module.finrank ℝ E)] in
lemma chartDensityOnE_differentiableAt_interior
    (g : SmoothRiemannianMetric I M) (α : M)
    {y : E} (hy : y ∈ interior (extChartAt I α).target) :
    DifferentiableAt ℝ (chartDensityOnE (I := I) g α) y := by
  have hcd_target : ContDiffOn ℝ ∞ (chartDensityOnE (I := I) g α)
      (extChartAt I α).target := chartDensityOnE_contDiffOn (I := I) g α
  have hcd_int : ContDiffOn ℝ ∞ (chartDensityOnE (I := I) g α)
      (interior (extChartAt I α).target) := hcd_target.mono interior_subset
  have hop_int : IsOpen (interior (extChartAt I α).target) := isOpen_interior
  have hy_nhd : interior (extChartAt I α).target ∈ 𝓝 y := hop_int.mem_nhds hy
  exact (hcd_int.contDiffAt hy_nhd).differentiableAt (by simp)

omit [NeZero (Module.finrank ℝ E)] in
private lemma partialDeriv_chartGramOnE_contDiffOn_interior
    (g : SmoothRiemannianMetric I M) (α : M)
    (j a b : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (partialDeriv (E := E) j (chartGramOnE (I := I) g α a b))
      (interior (extChartAt I α).target) := by
  classical
  have hG_target : ContDiffOn ℝ ∞ (chartGramOnE (I := I) g α a b)
      (extChartAt I α).target := chartGramOnE_contDiffOn (I := I) g α a b
  have hG_int : ContDiffOn ℝ ∞ (chartGramOnE (I := I) g α a b)
      (interior (extChartAt I α).target) := hG_target.mono interior_subset
  have hfderiv : ContDiffOn ℝ ∞ (fderiv ℝ (chartGramOnE (I := I) g α a b))
      (interior (extChartAt I α).target) :=
    hG_int.fderiv_of_isOpen isOpen_interior (by rw [ENat.coe_top_add_one])
  unfold partialDeriv
  exact hfderiv.clm_apply contDiffOn_const

omit [NeZero (Module.finrank ℝ E)] in
lemma partialDeriv_chartGramOnE_differentiableAt_interior
    (g : SmoothRiemannianMetric I M) (α : M)
    (j a b : Fin (Module.finrank ℝ E))
    {y : E} (hy : y ∈ interior (extChartAt I α).target) :
    DifferentiableAt ℝ
      (partialDeriv (E := E) j (chartGramOnE (I := I) g α a b)) y := by
  have hcd_int : ContDiffOn ℝ ∞
      (partialDeriv (E := E) j (chartGramOnE (I := I) g α a b))
      (interior (extChartAt I α).target) :=
    partialDeriv_chartGramOnE_contDiffOn_interior (I := I) g α j a b
  have hop_int : IsOpen (interior (extChartAt I α).target) := isOpen_interior
  have hy_nhd : interior (extChartAt I α).target ∈ 𝓝 y := hop_int.mem_nhds hy
  exact (hcd_int.contDiffAt hy_nhd).differentiableAt (by simp)

omit [NeZero (Module.finrank ℝ E)] in
private lemma partialDeriv_chartInvGramOnE_contDiffOn_interior
    (g : SmoothRiemannianMetric I M) (α : M)
    (j k l : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (partialDeriv (E := E) j (chartInvGramOnE (I := I) g α k l))
      (interior (extChartAt I α).target) := by
  classical
  have hG_target : ContDiffOn ℝ ∞ (chartInvGramOnE (I := I) g α k l)
      (extChartAt I α).target := chartInvGramOnE_contDiffOn (I := I) g α k l
  have hG_int : ContDiffOn ℝ ∞ (chartInvGramOnE (I := I) g α k l)
      (interior (extChartAt I α).target) := hG_target.mono interior_subset
  have hfderiv : ContDiffOn ℝ ∞ (fderiv ℝ (chartInvGramOnE (I := I) g α k l))
      (interior (extChartAt I α).target) :=
    hG_int.fderiv_of_isOpen isOpen_interior (by rw [ENat.coe_top_add_one])
  unfold partialDeriv
  exact hfderiv.clm_apply contDiffOn_const

omit [NeZero (Module.finrank ℝ E)] in
private lemma partialDeriv_chartInvGramOnE_differentiableAt_interior
    (g : SmoothRiemannianMetric I M) (α : M)
    (j k l : Fin (Module.finrank ℝ E))
    {y : E} (hy : y ∈ interior (extChartAt I α).target) :
    DifferentiableAt ℝ
      (partialDeriv (E := E) j (chartInvGramOnE (I := I) g α k l)) y := by
  have hcd_int : ContDiffOn ℝ ∞
      (partialDeriv (E := E) j (chartInvGramOnE (I := I) g α k l))
      (interior (extChartAt I α).target) :=
    partialDeriv_chartInvGramOnE_contDiffOn_interior (I := I) g α j k l
  have hop_int : IsOpen (interior (extChartAt I α).target) := isOpen_interior
  have hy_nhd : interior (extChartAt I α).target ∈ 𝓝 y := hop_int.mem_nhds hy
  exact (hcd_int.contDiffAt hy_nhd).differentiableAt (by simp)

end DivergenceTheorem
end Integral
end DifferentialGeometry
