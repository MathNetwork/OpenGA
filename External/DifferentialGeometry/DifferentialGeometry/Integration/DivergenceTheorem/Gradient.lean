import DifferentialGeometry.Integration.DivergenceTheorem.LocalFormula
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.TangentAction
import DifferentialGeometry.Integration.DivergenceTheorem.LocalFormula
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.ChartCoeffPullback
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import DifferentialGeometry.Integration.Volume.ChartDensity
import DifferentialGeometry.Integration.Volume.Family.Base
import DifferentialGeometry.Integration.Volume.Family.Variation
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Adjugate
import DifferentialGeometry.Geometry.Operator.Gradient





























































noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold Topology ContDiff Matrix

namespace DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure










private instance tangentSpace_finiteDimensional (x : M) :
    FiniteDimensional ℝ (TangentSpace I x) :=
  inferInstanceAs (FiniteDimensional ℝ E)


omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
private lemma metricFlatLinear_finrank_eq (x : M) :
    Module.finrank ℝ (TangentSpace I x) =
      Module.finrank ℝ (TangentSpace I x →ₗ[ℝ] ℝ) :=
  Subspace.dual_finrank_eq.symm




omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
private lemma hasMFDerivAt_rexp
    {f : M → ℝ} {x : M} {f' : TangentSpace I x →L[ℝ] ℝ}
    (hf : HasMFDerivAt I 𝓘(ℝ, ℝ) f x f') :
    HasMFDerivAt I 𝓘(ℝ, ℝ) (fun y : M => Real.exp (f y)) x
      (Real.exp (f x) • f') := by
  refine ⟨Real.continuous_exp.continuousAt.comp hf.1, ?_⟩
  simpa [writtenInExtChartAt, Function.comp_def] using hf.2.exp


omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
lemma mfderiv_exp_neg_toLinearMap
    {f : M → ℝ} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x) :
    (mfderiv I 𝓘(ℝ, ℝ) (fun y : M => Real.exp (-(f y))) x).toLinearMap =
      (-Real.exp (-(f x))) •
        (mfderiv I 𝓘(ℝ, ℝ) f x).toLinearMap := by
  have hmf :
      mfderiv I 𝓘(ℝ, ℝ) (fun y : M => Real.exp (-(f y))) x =
        (-Real.exp (-(f x))) • mfderiv I 𝓘(ℝ, ℝ) f x := by
    simpa [Pi.neg_apply, neg_smul] using
      (hasMFDerivAt_rexp (I := I) hf.hasMFDerivAt.neg).mfderiv
  rw [hmf]
  ext v
  rfl


lemma gradFun_exp_neg
    (g : SmoothRiemannianMetric I M) {f : M → ℝ} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x) :
    gradFun (I := I) g (fun y : M => Real.exp (-(f y))) x =
      (-Real.exp (-(f x))) • gradFun (I := I) g f x := by
  unfold gradFun metricSharp
  rw [mfderiv_exp_neg_toLinearMap (I := I) hf]
  exact LinearEquiv.map_smul
    (metricFlatMap (I := I) g x).symm
    (-Real.exp (-(f x)))
    (mfderiv I 𝓘(ℝ, ℝ) f x).toLinearMap




private lemma chartGramMatrixOnE_entry_contDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (fun y : E =>
        chartGramMatrix (I := I) g α ((extChartAt I α).symm y) i j)
      (extChartAt I α).target := by
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

omit [FiniteDimensional ℝ E] in
private lemma hasDerivAt_line_of_differentiableAt
    {F : E → ℝ} {y₀ : E} (v : E)
    (hF : DifferentiableAt ℝ F y₀) :
    HasDerivAt (fun t : ℝ => F (y₀ + t • v))
      (fderiv ℝ F y₀ v) 0 := by
  have hline : HasDerivAt (fun t : ℝ => y₀ + t • v) v 0 := by
    have hscale : HasDerivAt (fun t : ℝ => t • v) v 0 := by
      simpa using (hasDerivAt_id' (x := (0 : ℝ))).smul_const v
    have hsum : HasDerivAt (fun t : ℝ => y₀ + t • v) (0 + v) 0 :=
      (hasDerivAt_const (x := (0 : ℝ)) (c := y₀)).add hscale
    simpa using hsum
  have hcomp :=
    hF.hasFDerivAt.comp_hasDerivAt_of_eq (x := (0 : ℝ)) hline (by simp)
  simpa [Function.comp] using hcomp

lemma chartInvGramMatrix_symm
    (g : SmoothRiemannianMetric I M) (α x : M)
    (i j : Fin (Module.finrank ℝ E)) :
    chartInvGramMatrix (I := I) g α x j i =
      chartInvGramMatrix (I := I) g α x i j := by
  have hherm :
      (chartInvGramMatrix (I := I) g α x).IsHermitian := by
    unfold chartInvGramMatrix
    exact (chartGramMatrix_isHermitian (I := I) g α x).inv
  simpa using hherm.apply i j

private lemma chartGramMatrixOnE_partial_symm
    (g : SmoothRiemannianMetric I M) (α : M)
    (p i j : Fin (Module.finrank ℝ E)) (y : E) :
    partialDeriv (E := E) p
        (fun z : E =>
          chartGramMatrix (I := I) g α ((extChartAt I α).symm z) j i) y =
      partialDeriv (E := E) p
        (fun z : E =>
          chartGramMatrix (I := I) g α ((extChartAt I α).symm z) i j) y := by
  congr 2
  funext z
  have h := chartGramMatrix_isHermitian (I := I) g α ((extChartAt I α).symm z)
  simpa using h.apply i j

private lemma trace_invGram_mul_partialGram
    (g : SmoothRiemannianMetric I M) (α x : M)
    (p : Fin (Module.finrank ℝ E)) (y : E) :
    Matrix.trace
        (chartInvGramMatrix (I := I) g α x *
          Matrix.of (fun i j : Fin (Module.finrank ℝ E) =>
            partialDeriv (E := E) p
              (fun z : E =>
                chartGramMatrix (I := I) g α ((extChartAt I α).symm z) i j) y))
      =
    ∑ i : Fin (Module.finrank ℝ E),
      ∑ j : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g α x i j *
          partialDeriv (E := E) p
            (fun z : E =>
              chartGramMatrix (I := I) g α ((extChartAt I α).symm z) i j) y := by
  classical
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.of_apply]
  calc
    (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g α x i j *
            partialDeriv (E := E) p
              (fun z : E =>
                chartGramMatrix (I := I) g α ((extChartAt I α).symm z) j i) y)
        =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g α x i j *
            partialDeriv (E := E) p
              (fun z : E =>
                chartGramMatrix (I := I) g α ((extChartAt I α).symm z) i j) y := by
      refine Finset.sum_congr rfl ?_
      intro i _
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [chartGramMatrixOnE_partial_symm (I := I) g α p i j y]
    _ = _ := rfl



theorem chartDensityOnE_partial_div_eq_half_trace_invGram_partialGram
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M)
    (p : Fin (Module.finrank ℝ E)) :
    partialDeriv (E := E) p (chartDensityOnE (I := I) g x) (extChartAt I x x) /
        chartDensityOnE (I := I) g x (extChartAt I x x)
      =
    (1 / 2 : ℝ) *
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g x x i j *
            partialDeriv (E := E) p
              (fun y : E =>
                chartGramMatrix (I := I) g x ((extChartAt I x).symm y) i j)
              (extChartAt I x x) := by
  classical
  let y₀ : E := extChartAt I x x
  let v : E := (chartModelBasis E) p
  let Gline : ℝ → Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    fun t => chartGramMatrix (I := I) g x ((extChartAt I x).symm (y₀ + t • v))
  let Gprime : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    Matrix.of fun i j =>
      partialDeriv (E := E) p
        (fun y : E => chartGramMatrix (I := I) g x ((extChartAt I x).symm y) i j) y₀
  have hxsrc : x ∈ (extChartAt I x).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]
    exact mem_chart_source H x
  have hy₀_target : y₀ ∈ (extChartAt I x).target := by
    simp [y₀, (extChartAt I x).map_source hxsrc]
  have htarget_nhd : (extChartAt I x).target ∈ 𝓝 y₀ :=
    (isOpen_extChartAt_target (I := I) x).mem_nhds hy₀_target
  have hsymm_y₀ : (extChartAt I x).symm y₀ = x := by
    simp [y₀, (extChartAt I x).left_inv hxsrc]
  have hxbase : x ∈ (trivializationAt E (TangentSpace I) x).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source]
    exact mem_chart_source H x
  have hρ_pos : 0 < chartDensityOnE (I := I) g x y₀ := by
    simpa [chartDensityOnE, y₀, hsymm_y₀] using
      chartDensity_pos (I := I) g x hxbase
  have hρ_ne : chartDensityOnE (I := I) g x y₀ ≠ 0 := ne_of_gt hρ_pos
  have hρ_diff : DifferentiableAt ℝ (chartDensityOnE (I := I) g x) y₀ := by
    have hsmooth : ContDiffOn ℝ ∞ (chartDensityOnE (I := I) g x)
        (extChartAt I x).target :=
      chartDensityOnE_contDiffOn (I := I) g x
    exact ((hsmooth y₀ hy₀_target).contDiffAt htarget_nhd).differentiableAt
      (by simp)
  have hρ_line : HasDerivAt
      (fun t : ℝ => chartDensityOnE (I := I) g x (y₀ + t • v))
      (partialDeriv (E := E) p (chartDensityOnE (I := I) g x) y₀) 0 := by
    simpa [partialDeriv, v] using
      hasDerivAt_line_of_differentiableAt (E := E)
        (F := chartDensityOnE (I := I) g x) (y₀ := y₀) v hρ_diff
  have hEntries : ∀ i j : Fin (Module.finrank ℝ E),
      HasDerivAt (fun t : ℝ => Gline t i j) (Gprime i j) 0 := by
    intro i j
    have hentry_diff : DifferentiableAt ℝ
        (fun y : E => chartGramMatrix (I := I) g x ((extChartAt I x).symm y) i j)
        y₀ := by
      have hsmooth : ContDiffOn ℝ ∞
          (fun y : E => chartGramMatrix (I := I) g x ((extChartAt I x).symm y) i j)
          (extChartAt I x).target :=
        chartGramMatrixOnE_entry_contDiffOn (I := I) g x i j
      exact ((hsmooth y₀ hy₀_target).contDiffAt htarget_nhd).differentiableAt
        (by simp)
    simpa [Gline, Gprime, partialDeriv, v] using
      hasDerivAt_line_of_differentiableAt (E := E)
        (F := fun y : E =>
          chartGramMatrix (I := I) g x ((extChartAt I x).symm y) i j)
        (y₀ := y₀) v hentry_diff
  have hpos_det : 0 < (Gline 0).det := by
    simpa [Gline, y₀, v, hsymm_y₀] using
      chartGramMatrix_det_pos (I := I) g x hxbase
  have hjac := hasDerivAt_sqrt_det_eq_half_trace_inv_mul
    (G := Gline) (G' := Gprime) (t := (0 : ℝ)) hEntries hpos_det
  have hjacρ : HasDerivAt
      (fun t : ℝ => chartDensityOnE (I := I) g x (y₀ + t • v))
      ((1 / 2 : ℝ) *
        Matrix.trace ((chartGramMatrix (I := I) g x x)⁻¹ * Gprime) *
          chartDensityOnE (I := I) g x y₀) 0 := by
    simpa [Gline, Gprime, chartDensityOnE, chartDensity, y₀, v, hsymm_y₀] using hjac
  have hderiv :
      partialDeriv (E := E) p (chartDensityOnE (I := I) g x) y₀ =
        ((1 / 2 : ℝ) *
          Matrix.trace ((chartGramMatrix (I := I) g x x)⁻¹ * Gprime) *
            chartDensityOnE (I := I) g x y₀) :=
    hρ_line.unique hjacρ
  have htrace :
      Matrix.trace ((chartGramMatrix (I := I) g x x)⁻¹ * Gprime) =
        ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g x x i j *
              partialDeriv (E := E) p
                (fun y : E =>
                  chartGramMatrix (I := I) g x ((extChartAt I x).symm y) i j)
                y₀ := by
    simpa [Gprime, chartInvGramMatrix] using
      trace_invGram_mul_partialGram (I := I) (M := M) g x x p y₀
  calc
    partialDeriv (E := E) p (chartDensityOnE (I := I) g x) (extChartAt I x x) /
        chartDensityOnE (I := I) g x (extChartAt I x x)
        = partialDeriv (E := E) p (chartDensityOnE (I := I) g x) y₀ /
            chartDensityOnE (I := I) g x y₀ := by rfl
    _ = ((1 / 2 : ℝ) *
          Matrix.trace ((chartGramMatrix (I := I) g x x)⁻¹ * Gprime) *
            chartDensityOnE (I := I) g x y₀) /
          chartDensityOnE (I := I) g x y₀ := by rw [hderiv]
    _ = (1 / 2 : ℝ) *
          Matrix.trace ((chartGramMatrix (I := I) g x x)⁻¹ * Gprime) := by
      field_simp [hρ_ne]
    _ = (1 / 2 : ℝ) *
        ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g x x i j *
              partialDeriv (E := E) p
                (fun y : E =>
                  chartGramMatrix (I := I) g x ((extChartAt I x).symm y) i j)
                (extChartAt I x x) := by
      rw [htrace]









private lemma gradChartCoeff_contMDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (i : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞ (gradChartCoeff (I := I) g α f i)
      ((extChartAt I α).source ∩
        (extChartAt I α) ⁻¹' interior (extChartAt I α).target) := by
  classical
  refine contMDiffOn_finset_sum (fun j _ => ?_)
  refine ContMDiffOn.mul ?_ ?_
  ·
    have h1 : ContMDiffOn I 𝓘(ℝ) ∞
        (fun x => chartInvGramMatrix (I := I) g α x i j)
        (trivializationAt E (TangentSpace I) α).baseSet :=
      chartInvGramMatrix_entry_contMDiffOn (I := I) g α i j
    refine h1.mono ?_
    intro x hx
    rw [trivializationAt_baseSet_eq_chartAt_source]
    have := hx.1
    rw [extChartAt_source_eq_chartAt_source (I := I)] at this
    exact this
  ·
    have hpartial : ContDiffOn ℝ ∞
        (partialDeriv (E := E) j (scalarOnE (I := I) α f))
        (interior (extChartAt I α).target) := by
      have hbase : ContDiffOn ℝ ∞
          (scalarOnE (I := I) α f) (extChartAt I α).target :=
        scalarOnE_contDiffOn (I := I) α hf
      have hbase_int : ContDiffOn ℝ ∞ (scalarOnE (I := I) α f)
          (interior (extChartAt I α).target) := hbase.mono interior_subset
      have hfderiv : ContDiffOn ℝ ∞ (fderiv ℝ (scalarOnE (I := I) α f))
          (interior (extChartAt I α).target) :=
        hbase_int.fderiv_of_isOpen isOpen_interior (by rw [ENat.coe_top_add_one])
      have hconst : ContDiffOn ℝ ∞ (fun _ : E => (chartModelBasis E) j)
          (interior (extChartAt I α).target) := contDiffOn_const
      exact hfderiv.clm_apply hconst
    have hpartialM : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) ∞
        (partialDeriv (E := E) j (scalarOnE (I := I) α f))
        (interior (extChartAt I α).target) := hpartial.contMDiffOn
    have hchart : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I α : M → E)
        (chartAt H α).source := contMDiffOn_extChartAt
    have hchart' : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I α : M → E)
        ((extChartAt I α).source ∩
          (extChartAt I α) ⁻¹' interior (extChartAt I α).target) := by
      refine hchart.mono ?_
      intro x hx
      have h1 : x ∈ (extChartAt I α).source := hx.1
      rw [extChartAt_source_eq_chartAt_source (I := I)] at h1
      exact h1
    have hsubset : (extChartAt I α).source ∩
        (extChartAt I α) ⁻¹' interior (extChartAt I α).target ⊆
          (extChartAt I α : M → E) ⁻¹' interior (extChartAt I α).target :=
      fun _ hx => hx.2
    exact hpartialM.comp hchart' hsubset



private lemma gradChartLocal_contMDiffOn_total
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E x (gradChartLocal (I := I) g α f x))
      ((extChartAt I α).source ∩
        (extChartAt I α) ⁻¹' interior (extChartAt I α).target) := by
  classical


  have hcoeff : ∀ i, ContMDiffOn I 𝓘(ℝ) ∞ (gradChartCoeff (I := I) g α f i)
      ((extChartAt I α).source ∩
        (extChartAt I α) ⁻¹' interior (extChartAt I α).target) :=
    fun i => gradChartCoeff_contMDiffOn (I := I) g α hf i
  have hbasis : ∀ i, ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E x (chartBasisVecFiber (I := I) α i x))
      ((extChartAt I α).source ∩
        (extChartAt I α) ⁻¹' interior (extChartAt I α).target) := by
    intro i
    refine (chartBasisVec_contMDiffOn (I := I) α i).mono ?_
    intro x hx
    rw [trivializationAt_baseSet_eq_chartAt_source]
    have := hx.1
    rw [extChartAt_source_eq_chartAt_source (I := I)] at this
    exact this
  have hsmul : ∀ i, ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E x
        (gradChartCoeff (I := I) g α f i x • chartBasisVecFiber (I := I) α i x))
      ((extChartAt I α).source ∩
        (extChartAt I α) ⁻¹' interior (extChartAt I α).target) := by
    intro i
    exact (hcoeff i).smul_section (hbasis i)

  have hsum : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E x
        (∑ i, gradChartCoeff (I := I) g α f i x •
          chartBasisVecFiber (I := I) α i x))
      ((extChartAt I α).source ∩
        (extChartAt I α) ⁻¹' interior (extChartAt I α).target) :=
    ContMDiffOn.sum_section (fun i _ => hsmul i)
  exact hsum



private lemma gradChartLocal_contMDiffOn_total_baseSet [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E x (gradChartLocal (I := I) g α f x))
      (chartAt H α).source := by
  refine (gradChartLocal_contMDiffOn_total (I := I) g α hf).mono ?_
  intro x hx
  refine ⟨?_, ?_⟩
  · rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hx
  · rw [show (extChartAt I α : M → E) ⁻¹' interior (extChartAt I α).target =
          (extChartAt I α : M → E) ⁻¹' (extChartAt I α).target from ?_]
    · exact (extChartAt I α).map_source
        (by rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hx)
    · congr 1
      exact (isOpen_extChartAt_target (I := I) α).interior_eq


theorem tangentSectionAction_grad_g_eq_inner [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    tangentSectionAction (I := I) X f x =
      g.inner x (X x)
        ((grad_g (I := I) g hf : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) := by
  rw [grad_g_apply]
  rw [inner_gradFun_right (I := I) g f x (X x)]
  rfl




end DifferentialGeometry.Integral.DivergenceTheorem
