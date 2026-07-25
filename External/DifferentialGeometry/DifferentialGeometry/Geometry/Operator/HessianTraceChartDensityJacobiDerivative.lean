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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]   [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure

private noncomputable def basisDirectionLine (y₀ : E) (l : Fin (Module.finrank ℝ E)) :
    ℝ → E := fun s => y₀ + s • (chartModelBasis E) l

omit [NeZero (Module.finrank ℝ E)] in
private lemma hasDerivAt_jacobiLine (y₀ : E) (l : Fin (Module.finrank ℝ E))
    (s : ℝ) :
    HasDerivAt (basisDirectionLine (E := E) y₀ l) ((chartModelBasis E) l) s := by
  have h₁ : HasDerivAt (fun s : ℝ => s • (chartModelBasis E) l)
      ((1 : ℝ) • (chartModelBasis E) l) s :=
    (hasDerivAt_id s).smul_const ((chartModelBasis E) l)
  have h₁' : HasDerivAt (fun s : ℝ => s • (chartModelBasis E) l)
      ((chartModelBasis E) l) s := by
    rw [show ((1 : ℝ) • (chartModelBasis E) l) = (chartModelBasis E) l from
      one_smul ℝ _] at h₁
    exact h₁
  have h₂ : HasDerivAt (fun _ : ℝ => y₀) (0 : E) s := hasDerivAt_const s y₀
  have h := h₂.add h₁'
  have hcoerce : (0 : E) + (chartModelBasis E) l = (chartModelBasis E) l := zero_add _
  rw [hcoerce] at h
  have hfun_eq : (fun s : ℝ => y₀ + s • (chartModelBasis E) l) =
      basisDirectionLine (E := E) y₀ l := by
    funext s; rfl
  have h' : HasDerivAt (fun s : ℝ => y₀ + s • (chartModelBasis E) l)
      ((chartModelBasis E) l) s := by
    have hpoint : ((fun _ : ℝ => y₀) + fun s : ℝ => s • (chartModelBasis E) l) =
        (fun s : ℝ => y₀ + s • (chartModelBasis E) l) := by
      funext s; simp [Pi.add_apply]
    rw [hpoint] at h
    exact h
  rw [← hfun_eq]
  exact h'

omit [NeZero (Module.finrank ℝ E)] in
private lemma hasDerivAt_comp_jacobiLine
    {y₀ : E} {l : Fin (Module.finrank ℝ E)} {F : E → ℝ}
    (hF : DifferentiableAt ℝ F y₀) :
    HasDerivAt (fun s : ℝ => F (basisDirectionLine (E := E) y₀ l s))
      (partialDeriv (E := E) l F y₀) 0 := by
  have hy : (basisDirectionLine (E := E) y₀ l 0) = y₀ := by
    unfold basisDirectionLine; rw [zero_smul, add_zero]
  have hF' : HasFDerivAt F (fderiv ℝ F y₀) y₀ := hF.hasFDerivAt
  have hF'' : HasFDerivAt F (fderiv ℝ F y₀) (basisDirectionLine (E := E) y₀ l 0) := by
    rw [hy]; exact hF'
  have hline := hasDerivAt_jacobiLine (E := E) y₀ l 0
  have := hF''.comp_hasDerivAt 0 hline
  exact this

private noncomputable def gramJacobiFamily
    (g : SmoothRiemannianMetric I M) (α : M)
    (y₀ : E) (l : Fin (Module.finrank ℝ E)) :
    ℝ → Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  fun s => Matrix.of fun i j =>
    chartGramOnE (I := I) g α i j (basisDirectionLine (E := E) y₀ l s)

omit [NeZero (Module.finrank ℝ E)] in
private lemma gramJacobiFamily_zero
    (g : SmoothRiemannianMetric I M) (α : M)
    (y₀ : E) (l : Fin (Module.finrank ℝ E)) :
    gramJacobiFamily (I := I) g α y₀ l 0 =
      Matrix.of fun i j => chartGramOnE (I := I) g α i j y₀ := by
  unfold gramJacobiFamily basisDirectionLine
  ext i j
  simp [zero_smul, add_zero]

omit [NeZero (Module.finrank ℝ E)] in
private lemma gramAtY_eq_chartGramMatrix
    (g : SmoothRiemannianMetric I M) (α : M) (y₀ : E) :
    (Matrix.of fun i j => chartGramOnE (I := I) g α i j y₀) =
      chartGramMatrix (I := I) g α ((extChartAt I α).symm y₀) := by
  ext i j
  rfl

omit [NeZero (Module.finrank ℝ E)] in
private lemma hasDerivAt_gramJacobiFamily_entry
    (g : SmoothRiemannianMetric I M) (α : M)
    (y₀ : E) (l : Fin (Module.finrank ℝ E))
    (i j : Fin (Module.finrank ℝ E))
    (hy : y₀ ∈ interior (extChartAt I α).target) :
    HasDerivAt (fun s : ℝ => gramJacobiFamily (I := I) g α y₀ l s i j)
      (partialDeriv (E := E) l (chartGramOnE (I := I) g α i j) y₀) 0 := by
  have hG : DifferentiableAt ℝ (chartGramOnE (I := I) g α i j) y₀ :=
    chartGramOnE_differentiableAt_interior (I := I) g α i j hy
  have h := hasDerivAt_comp_jacobiLine (E := E) (l := l) (F := chartGramOnE (I := I) g α i j) hG
  unfold gramJacobiFamily
  simp only [Matrix.of_apply]
  exact h

omit [NeZero (Module.finrank ℝ E)] in
private lemma gramJacobiFamily_det_pos
    (g : SmoothRiemannianMetric I M) (α : M)
    (y₀ : E) (l : Fin (Module.finrank ℝ E))
    (hy : y₀ ∈ (extChartAt I α).target) :
    0 < (gramJacobiFamily (I := I) g α y₀ l 0).det := by
  rw [gramJacobiFamily_zero, gramAtY_eq_chartGramMatrix]
  have hbase : (extChartAt I α).symm y₀ ∈
      (trivializationAt E (TangentSpace I) α).baseSet := by
    have hsource : (extChartAt I α).symm y₀ ∈ (extChartAt I α).source :=
      (extChartAt I α).map_target hy
    rw [extChartAt_source_eq_chartAt_source (I := I)] at hsource
    rw [trivializationAt_baseSet_eq_chartAt_source]
    exact hsource
  exact chartGramMatrix_det_pos (I := I) g α hbase

omit [NeZero (Module.finrank ℝ E)] in
private lemma partialDeriv_det_chartGramOnE
    (g : SmoothRiemannianMetric I M) (α : M)
    (y₀ : E) (l : Fin (Module.finrank ℝ E))
    (hy : y₀ ∈ interior (extChartAt I α).target) :
    partialDeriv (E := E) l
        (fun y : E => (chartGramMatrix (I := I) g α ((extChartAt I α).symm y)).det) y₀ =
      (chartGramMatrix (I := I) g α ((extChartAt I α).symm y₀)).det *
        Matrix.trace ((chartGramMatrix (I := I) g α ((extChartAt I α).symm y₀))⁻¹ *
          Matrix.of (fun i j => partialDeriv (E := E) l
            (chartGramOnE (I := I) g α i j) y₀)) := by
  classical
  have hytgt : y₀ ∈ (extChartAt I α).target := interior_subset hy
  set Gf := gramJacobiFamily (I := I) g α y₀ l with hGf
  have hentries : ∀ i j : Fin (Module.finrank ℝ E),
      HasDerivAt (fun s => Gf s i j)
        (partialDeriv (E := E) l (chartGramOnE (I := I) g α i j) y₀) 0 :=
    fun i j => hasDerivAt_gramJacobiFamily_entry (I := I) g α y₀ l i j hy
  have hpos : 0 < (Gf 0).det := gramJacobiFamily_det_pos (I := I) g α y₀ l hytgt
  have hunit : IsUnit (Gf 0).det := (ne_of_gt hpos).isUnit
  have hjac :=
    DifferentialGeometry.Integral.Measure.hasDerivAt_det_eq_det_mul_trace_inv_mul
      (n := Fin (Module.finrank ℝ E))
      Gf
      (Matrix.of (fun i j =>
        partialDeriv (E := E) l (chartGramOnE (I := I) g α i j) y₀))
      0 (fun i j => by simpa [Matrix.of_apply] using hentries i j) hunit
  have hfun_eq : (fun s : ℝ => (Gf s).det) =
      fun s : ℝ => (chartGramMatrix (I := I) g α
        ((extChartAt I α).symm (basisDirectionLine (E := E) y₀ l s))).det := by
    funext s
    have hmat_eq : Gf s = chartGramMatrix (I := I) g α
        ((extChartAt I α).symm (basisDirectionLine (E := E) y₀ l s)) := by
      rw [hGf]
      ext i j
      rfl
    rw [hmat_eq]
  rw [hfun_eq] at hjac
  have hDF : DifferentiableAt ℝ
      (fun y : E => (chartGramMatrix (I := I) g α ((extChartAt I α).symm y)).det) y₀ := by
    have hdet_smooth : ContDiffOn ℝ ∞
        (fun y : E => (chartGramMatrix (I := I) g α ((extChartAt I α).symm y)).det)
        (extChartAt I α).target := by
      have hexp : (fun y : E =>
            (chartGramMatrix (I := I) g α ((extChartAt I α).symm y)).det) =
          (fun y : E =>
            ∑ σ : Equiv.Perm (Fin (Module.finrank ℝ E)),
              ((Equiv.Perm.sign σ : ℤ) : ℝ) *
                ∏ i, chartGramOnE (I := I) g α (σ i) i y) := by
        funext y
        rw [Matrix.det_apply]
        simp only [Units.smul_def, zsmul_eq_mul]
        rfl
      rw [hexp]
      refine ContDiffOn.sum (fun σ _ => ?_)
      refine ContDiffOn.mul contDiffOn_const ?_
      refine contDiffOn_prod (fun i _ => ?_)
      exact chartGramOnE_contDiffOn (I := I) g α (σ i) i
    have hcd_int : ContDiffOn ℝ ∞
        (fun y : E => (chartGramMatrix (I := I) g α ((extChartAt I α).symm y)).det)
        (interior (extChartAt I α).target) := hdet_smooth.mono interior_subset
    have hop_int : IsOpen (interior (extChartAt I α).target) := isOpen_interior
    have hy_nhd : interior (extChartAt I α).target ∈ 𝓝 y₀ := hop_int.mem_nhds hy
    exact (hcd_int.contDiffAt hy_nhd).differentiableAt (by simp)
  have hcomp := hasDerivAt_comp_jacobiLine (E := E) (l := l)
    (F := fun y : E => (chartGramMatrix (I := I) g α ((extChartAt I α).symm y)).det)
    hDF
  have heq := hjac.unique hcomp
  have hGf_zero_eq : Gf 0 =
      chartGramMatrix (I := I) g α ((extChartAt I α).symm y₀) := by
    rw [hGf, gramJacobiFamily_zero, gramAtY_eq_chartGramMatrix]
  rw [hGf_zero_eq] at heq
  exact heq.symm

omit [NeZero (Module.finrank ℝ E)] in
lemma partialDeriv_chartDensityOnE
    (g : SmoothRiemannianMetric I M) (α : M)
    (y₀ : E) (l : Fin (Module.finrank ℝ E))
    (hy : y₀ ∈ interior (extChartAt I α).target) :
    partialDeriv (E := E) l (chartDensityOnE (I := I) g α) y₀ =
      (1 / 2) *
        Matrix.trace ((chartGramMatrix (I := I) g α ((extChartAt I α).symm y₀))⁻¹ *
          Matrix.of (fun i j => partialDeriv (E := E) l
            (chartGramOnE (I := I) g α i j) y₀)) *
        chartDensityOnE (I := I) g α y₀ := by
  classical
  have hytgt : y₀ ∈ (extChartAt I α).target := interior_subset hy
  set Gf := gramJacobiFamily (I := I) g α y₀ l with hGf
  have hentries : ∀ i j : Fin (Module.finrank ℝ E),
      HasDerivAt (fun s => Gf s i j)
        (partialDeriv (E := E) l (chartGramOnE (I := I) g α i j) y₀) 0 :=
    fun i j => hasDerivAt_gramJacobiFamily_entry (I := I) g α y₀ l i j hy
  have hpos : 0 < (Gf 0).det := gramJacobiFamily_det_pos (I := I) g α y₀ l hytgt
  have hjac :=
    DifferentialGeometry.Integral.Measure.hasDerivAt_sqrt_det_eq_half_trace_inv_mul
      (n := Fin (Module.finrank ℝ E))
      Gf
      (Matrix.of (fun i j =>
        partialDeriv (E := E) l (chartGramOnE (I := I) g α i j) y₀))
      0 (fun i j => by simpa [Matrix.of_apply] using hentries i j) hpos
  have hfun_eq : (fun s : ℝ => Real.sqrt (Gf s).det) =
      fun s : ℝ => chartDensityOnE (I := I) g α (basisDirectionLine (E := E) y₀ l s) := by
    funext s
    have hmat_eq : Gf s = chartGramMatrix (I := I) g α
        ((extChartAt I α).symm (basisDirectionLine (E := E) y₀ l s)) := by
      rw [hGf]
      ext i j
      rfl
    rw [hmat_eq]
    rfl
  rw [hfun_eq] at hjac
  have hDF : DifferentiableAt ℝ (chartDensityOnE (I := I) g α) y₀ :=
    chartDensityOnE_differentiableAt_interior (I := I) g α hy
  have hcomp := hasDerivAt_comp_jacobiLine (E := E) (l := l)
    (F := chartDensityOnE (I := I) g α) hDF
  have heq := hjac.unique hcomp
  have hGf_zero_eq : Gf 0 =
      chartGramMatrix (I := I) g α ((extChartAt I α).symm y₀) := by
    rw [hGf, gramJacobiFamily_zero, gramAtY_eq_chartGramMatrix]
  have hsqrt_eq :
      Real.sqrt (chartGramMatrix (I := I) g α ((extChartAt I α).symm y₀)).det =
        chartDensityOnE (I := I) g α y₀ := rfl
  rw [hGf_zero_eq] at heq
  rw [hsqrt_eq] at heq
  exact heq.symm

end DivergenceTheorem
end Integral
end DifferentialGeometry
