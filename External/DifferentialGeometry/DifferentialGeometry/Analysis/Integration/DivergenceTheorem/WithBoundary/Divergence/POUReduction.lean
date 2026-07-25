import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.WithBoundary.Divergence.LocalFormula
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.WithBoundary.Divergence.PartialDerivWithin
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.WithBoundary.Divergence.Global
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.LocalFormula
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.POUReduction
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.TangentAction
import DifferentialGeometry.Analysis.Integration.Measure.RiemannianMeasure
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection


noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold Topology ContDiff Matrix

namespace DifferentialGeometry
namespace Integral
namespace DivergenceTheorem
namespace WithBoundary

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure

example (φ : M → ℝ) (hφ : ContMDiff I 𝓘(ℝ) ∞ φ)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    (smoothSmul
        (I := I) φ hφ X) x = φ x • X x := rfl

omit [InnerProductSpace ℝ E] [Module.Finite ℝ E] in
private lemma scalarOnE_mdifferentiableWithinAt_target
    (α : M) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    {y : E} (hy : y ∈ (extChartAt I α).target) :
    MDifferentiableWithinAt 𝓘(ℝ, E) 𝓘(ℝ)
      (scalarOnE (I := I) α f) (extChartAt I α).target y := by
  have hcont : ContDiffWithinAt ℝ ∞ (scalarOnE (I := I) α f)
      (extChartAt I α).target y :=
    scalarOnE_contDiffWithinAt (I := I) α hf hy
  have hdiff : DifferentiableWithinAt ℝ (scalarOnE (I := I) α f)
      (extChartAt I α).target y :=
    hcont.differentiableWithinAt (by simp)
  exact hdiff.mdifferentiableWithinAt

omit [InnerProductSpace ℝ E] [Module.Finite ℝ E] [IsManifold I ∞ M] in
private lemma extChartAt_mapsTo_target_chart_source (α : M) :
    Set.MapsTo (extChartAt I α : M → E) (chartAt H α).source
      (extChartAt I α).target := by
  intro x hx
  have hx' : x ∈ (extChartAt I α).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hx
  exact (extChartAt I α).map_source hx'

omit [InnerProductSpace ℝ E] in
private lemma mfderiv_extChartAt_chartBasisVecFiber
    (α : M) {x : M} (hx : x ∈ (chartAt H α).source)
    (i : Fin (Module.finrank ℝ E)) :
    mfderiv I 𝓘(ℝ, E) (extChartAt I α) x
        (chartBasisVecFiber (I := I) α i x)
      = (chartModelBasis E) i := by
  classical
  let T : Bundle.Trivialization E (π E (TangentSpace I : M → Type _)) :=
    trivializationAt E (TangentSpace I) α
  have hT_def : T = trivializationAt E (TangentSpace I) α := rfl
  have hbase : x ∈ T.baseSet := by
    change x ∈ (trivializationAt E (TangentSpace I) α).baseSet
    rw [trivializationAt_baseSet_eq_chartAt_source]; exact hx
  have hmfderiv_eq :
      mfderiv I 𝓘(ℝ, E) (extChartAt I α) x =
        (T.continuousLinearMapAt ℝ x : TangentSpace I x →L[ℝ] E) := by
    change mfderiv I 𝓘(ℝ, E) (extChartAt I α) x =
      ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ x :
        TangentSpace I x →L[ℝ] E)
    exact (TangentBundle.continuousLinearMapAt_trivializationAt (𝕜 := ℝ) (I := I)
      (x₀ := α) (x := x) hx).symm
  rw [hmfderiv_eq]
  change T.continuousLinearMapAt ℝ x (T.symm x ((chartModelBasis E) i))
    = (chartModelBasis E) i
  rw [show T.symm x ((chartModelBasis E) i) =
        T.symmL ℝ x ((chartModelBasis E) i) from by
      rw [Trivialization.symmL_apply]]
  exact Trivialization.continuousLinearMapAt_symmL (R := ℝ) T (b := x) hbase
    ((chartModelBasis E) i)

omit [InnerProductSpace ℝ E] [Module.Finite ℝ E] [IsManifold I ∞ M] in
private lemma mfderivWithin_extChartAt_chart_source
    (α : M) {x : M} (hx : x ∈ (chartAt H α).source) :
    mfderivWithin I 𝓘(ℝ, E) (extChartAt I α : M → E) (chartAt H α).source x =
      mfderiv I 𝓘(ℝ, E) (extChartAt I α : M → E) x :=
  mfderivWithin_of_isOpen (chartAt H α).open_source hx

omit [InnerProductSpace ℝ E] [Module.Finite ℝ E] [IsManifold I ∞ M] in
private lemma mfderivWithin_chart_source_of_mdiff
    (α : M) {x : M} (hx : x ∈ (chartAt H α).source) (f : M → ℝ) :
    mfderivWithin I 𝓘(ℝ) f (chartAt H α).source x = mfderiv I 𝓘(ℝ) f x :=
  mfderivWithin_of_isOpen (chartAt H α).open_source hx

omit [InnerProductSpace ℝ E] [Module.Finite ℝ E] in
private lemma mfderiv_factor_through_extChartAt
    (α : M) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    {x : M} (hx : x ∈ (chartAt H α).source)
    (v : TangentSpace I x) :
    mfderiv I 𝓘(ℝ) f x v =
      (fderivWithin ℝ (scalarOnE (I := I) α f)
          (extChartAt I α).target ((extChartAt I α) x))
        ((mfderiv I 𝓘(ℝ, E) (extChartAt I α : M → E) x) v) := by
  classical
  set s : Set M := (chartAt H α).source with hs_def
  have hs_open : IsOpen s := (chartAt H α).open_source
  have hxs : x ∈ s := hx
  have hf_mdiff_at : MDifferentiableAt I 𝓘(ℝ) f x :=
    hf.mdifferentiableAt (by simp)
  have hphi_mdiff_at : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I α) x :=
    mdifferentiableAt_extChartAt (I := I) (x := α) hx
  set y₀ : E := (extChartAt I α) x
  have hy₀_target : y₀ ∈ (extChartAt I α).target :=
    extChartAt_mapsTo_target_chart_source (I := I) α hx
  have hf_mdiffWithin : MDifferentiableWithinAt I 𝓘(ℝ) f s x :=
    hf_mdiff_at.mdifferentiableWithinAt
  have hphi_mdiffWithin : MDifferentiableWithinAt I 𝓘(ℝ, E) (extChartAt I α) s x :=
    hphi_mdiff_at.mdifferentiableWithinAt
  have hsubset : s ⊆ (extChartAt I α : M → E) ⁻¹' (extChartAt I α).target :=
    fun z hz => extChartAt_mapsTo_target_chart_source (I := I) α hz
  have hscalar_mdiffWithin :
      MDifferentiableWithinAt 𝓘(ℝ, E) 𝓘(ℝ) (scalarOnE (I := I) α f)
        (extChartAt I α).target y₀ :=
    scalarOnE_mdifferentiableWithinAt_target (I := I) α hf hy₀_target
  have hcomp_eq : ∀ z ∈ s, f z = (scalarOnE (I := I) α f) ((extChartAt I α) z) := by
    intro z hz
    have hzsrc : z ∈ (extChartAt I α).source := by
      rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hz
    rw [scalarOnE_def, (extChartAt I α).left_inv hzsrc]
  have hcomp_evEq : f =ᶠ[𝓝 x] (scalarOnE (I := I) α f) ∘ (extChartAt I α) := by
    filter_upwards [hs_open.mem_nhds hxs] with z hz
    exact hcomp_eq z hz
  have huniq : UniqueMDiffWithinAt I s x := hs_open.uniqueMDiffWithinAt hxs
  have hcomp_within :
      mfderivWithin I 𝓘(ℝ) (Function.comp (scalarOnE (I := I) α f)
            (extChartAt I α : M → E)) s x =
        (mfderivWithin 𝓘(ℝ, E) 𝓘(ℝ) (scalarOnE (I := I) α f)
            (extChartAt I α).target y₀).comp
          (mfderivWithin I 𝓘(ℝ, E) (extChartAt I α : M → E) s x) :=
    mfderivWithin_comp x hscalar_mdiffWithin hphi_mdiffWithin hsubset huniq
  have hmfderiv_phi :
      mfderivWithin I 𝓘(ℝ, E) (extChartAt I α : M → E) s x =
        mfderiv I 𝓘(ℝ, E) (extChartAt I α : M → E) x :=
    mfderivWithin_extChartAt_chart_source (I := I) α hx
  have hmfderiv_f_eq :
      mfderiv I 𝓘(ℝ) f x =
        mfderiv I 𝓘(ℝ) (Function.comp (scalarOnE (I := I) α f)
            (extChartAt I α : M → E)) x :=
    Filter.EventuallyEq.mfderiv_eq hcomp_evEq
  have hmfderiv_comp_within_to_full :
      mfderivWithin I 𝓘(ℝ) (Function.comp (scalarOnE (I := I) α f)
            (extChartAt I α : M → E)) s x =
        mfderiv I 𝓘(ℝ) (Function.comp (scalarOnE (I := I) α f)
            (extChartAt I α : M → E)) x :=
    mfderivWithin_chart_source_of_mdiff (I := I) α hx _
  have hgoal_full :
      mfderiv I 𝓘(ℝ) f x =
        (mfderivWithin 𝓘(ℝ, E) 𝓘(ℝ) (scalarOnE (I := I) α f)
            (extChartAt I α).target y₀).comp
          (mfderiv I 𝓘(ℝ, E) (extChartAt I α : M → E) x) := by
    rw [hmfderiv_f_eq, ← hmfderiv_comp_within_to_full, hcomp_within, hmfderiv_phi]
  have hscalar_mfd_eq_fd :
      mfderivWithin 𝓘(ℝ, E) 𝓘(ℝ) (scalarOnE (I := I) α f)
          (extChartAt I α).target y₀ =
        fderivWithin ℝ (scalarOnE (I := I) α f)
          (extChartAt I α).target y₀ :=
    mfderivWithin_eq_fderivWithin
  rw [hgoal_full, hscalar_mfd_eq_fd]
  rfl

omit [InnerProductSpace ℝ E] in
private lemma mfderiv_chartBasisVecFiber_within
    (α : M) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    {x : M} (hx : x ∈ (chartAt H α).source)
    (i : Fin (Module.finrank ℝ E)) :
    mfderiv I 𝓘(ℝ) f x
        (chartBasisVecFiber (I := I) α i x) =
      partialDerivWithin (E := E) (extChartAt I α).target i
        (scalarOnE (I := I) α f) ((extChartAt I α) x) := by
  classical
  rw [mfderiv_factor_through_extChartAt (I := I) α hf hx
        (chartBasisVecFiber (I := I) α i x)]
  rw [mfderiv_extChartAt_chartBasisVecFiber (I := I) α hx i]
  rfl

omit [InnerProductSpace ℝ E] in
theorem tangentSectionAction_chartLocal_within
    (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    {x : M} (hx : x ∈ (chartAt H α).source) :
    tangentSectionAction (I := I) X f x =
      ∑ i : Fin (Module.finrank ℝ E),
        chartCoeff (I := I) α X i x *
          partialDerivWithin (E := E) (extChartAt I α).target i
            (scalarOnE (I := I) α f) ((extChartAt I α) x) := by
  classical
  have hbase : x ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source]; exact hx
  have hXrecomp : X x = ∑ i, chartCoeff (I := I) α X i x •
        chartBasisVecFiber (I := I) α i x :=
    chartCoeff_recompose (I := I) α X hbase
  rw [tangentSectionAction_def, hXrecomp]
  rw [map_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [map_smul]
  rw [mfderiv_chartBasisVecFiber_within (I := I) α hf hx i]
  exact smul_eq_mul ..

omit [InnerProductSpace ℝ E] in
private lemma chartCoeffOnE_mul_chartDensityOnE_differentiableWithinAt
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (i : Fin (Module.finrank ℝ E))
    {y : E} (hy : y ∈ (extChartAt I α).target) :
    DifferentiableWithinAt ℝ
      (fun z : E =>
        chartCoeffOnE (I := I) α X i z * chartDensityOnE (I := I) g α z)
      (extChartAt I α).target y := by
  have hsmooth : ContDiffOn ℝ ∞
      (fun z : E =>
        chartCoeffOnE (I := I) α X i z * chartDensityOnE (I := I) g α z)
      (extChartAt I α).target :=
    chartCoeffOnE_mul_chartDensityOnE_contDiffOn (I := I) g α X i
  exact (hsmooth y hy).differentiableWithinAt (by simp)

omit [InnerProductSpace ℝ E] [Module.Finite ℝ E] in
private lemma scalarOnE_differentiableWithinAt
    (α : M) {φ : M → ℝ} (hφ : ContMDiff I 𝓘(ℝ) ∞ φ)
    {y : E} (hy : y ∈ (extChartAt I α).target) :
    DifferentiableWithinAt ℝ (scalarOnE (I := I) α φ)
      (extChartAt I α).target y := by
  have hsmooth : ContDiffOn ℝ ∞ (scalarOnE (I := I) α φ) (extChartAt I α).target :=
    scalarOnE_contDiffOn (I := I) α hφ
  exact (hsmooth y hy).differentiableWithinAt (by simp)

omit [InnerProductSpace ℝ E] in
private lemma localDivergenceWithin_at_self_smoothSmul
    (g : SmoothRiemannianMetric I M) (x : M)
    (φ : M → ℝ) (hφ : ContMDiff I 𝓘(ℝ) ∞ φ)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    localDivergenceWithin (I := I) g x
        (smoothSmul
          (I := I) φ hφ X) x =
      φ x * localDivergenceWithin (I := I) g x X x +
        tangentSectionAction (I := I) X φ x := by
  classical
  set y₀ : E := extChartAt I x x with hy₀_def
  have hxsrc : x ∈ (extChartAt I x).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]
    exact mem_chart_source H x
  have hy₀_target : y₀ ∈ (extChartAt I x).target :=
    (extChartAt I x).map_source hxsrc
  have hbase : x ∈ (trivializationAt E (TangentSpace I) x).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source]
    exact mem_chart_source H x
  have hρ_pos : 0 < chartDensity (I := I) g x x :=
    chartDensity_pos (I := I) g x hbase
  have hρ_ne : chartDensity (I := I) g x x ≠ 0 := ne_of_gt hρ_pos
  have huniq : UniqueDiffWithinAt ℝ (extChartAt I x).target y₀ :=
    uniqueDiffOn_extChartAt_target_apply (I := I) x hy₀_target
  rw [localDivergenceWithin_def, localDivergenceWithin_def]
  set u : E → ℝ := scalarOnE (I := I) x φ with hu_def
  set v : Fin (Module.finrank ℝ E) → E → ℝ :=
    fun i y => chartCoeffOnE (I := I) x X i y * chartDensityOnE (I := I) g x y
    with hv_def
  have hintegrand_eq : ∀ y ∈ (extChartAt I x).target,
      ∀ i : Fin (Module.finrank ℝ E),
        chartCoeffOnE (I := I) x
          (smoothSmul
            (I := I) φ hφ X) i y *
          chartDensityOnE (I := I) g x y =
        u y * v i y := by
    intro y hy i
    rw [chartCoeffOnE_smoothSmul
      (I := I) x φ hφ X i hy]
    change scalarOnE (I := I) x φ y * chartCoeffOnE (I := I) x X i y *
        chartDensityOnE (I := I) g x y =
      u y * (chartCoeffOnE (I := I) x X i y * chartDensityOnE (I := I) g x y)
    ring
  have hpartial_eq : ∀ i : Fin (Module.finrank ℝ E),
      partialDerivWithin (E := E) (extChartAt I x).target i
        (fun y => chartCoeffOnE (I := I) x
          (smoothSmul
            (I := I) φ hφ X) i y *
          chartDensityOnE (I := I) g x y) y₀ =
      partialDerivWithin (E := E) (extChartAt I x).target i
        (fun y => u y * v i y) y₀ := by
    intro i
    refine partialDerivWithin_congr_of_eqOn_of_mem ?_ hy₀_target
    intro y hy
    exact hintegrand_eq y hy i
  have hu_diff : DifferentiableWithinAt ℝ u (extChartAt I x).target y₀ :=
    scalarOnE_differentiableWithinAt (I := I) x hφ hy₀_target
  have hv_diff : ∀ i : Fin (Module.finrank ℝ E),
      DifferentiableWithinAt ℝ (v i) (extChartAt I x).target y₀ :=
    fun i => chartCoeffOnE_mul_chartDensityOnE_differentiableWithinAt
      (I := I) g x X i hy₀_target
  have hLeibniz : ∀ i : Fin (Module.finrank ℝ E),
      partialDerivWithin (E := E) (extChartAt I x).target i
        (fun y => u y * v i y) y₀ =
        u y₀ * partialDerivWithin (E := E) (extChartAt I x).target i (v i) y₀ +
          v i y₀ * partialDerivWithin (E := E) (extChartAt I x).target i u y₀ := by
    intro i
    exact partialDerivWithin_mul (s := (extChartAt I x).target) (y := y₀) (i := i)
      u (v i) huniq hu_diff (hv_diff i)
  have hLHS_num :
      ∑ i : Fin (Module.finrank ℝ E),
        partialDerivWithin (E := E) (extChartAt I x).target i
          (fun y => chartCoeffOnE (I := I) x
            (smoothSmul
              (I := I) φ hφ X) i y *
            chartDensityOnE (I := I) g x y) y₀ =
      ∑ i : Fin (Module.finrank ℝ E),
        (u y₀ * partialDerivWithin (E := E) (extChartAt I x).target i (v i) y₀ +
          v i y₀ * partialDerivWithin (E := E) (extChartAt I x).target i u y₀) := by
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [hpartial_eq i, hLeibniz i]
  rw [hLHS_num]
  rw [Finset.sum_add_distrib]
  rw [show (∑ i : Fin (Module.finrank ℝ E),
            u y₀ * partialDerivWithin (E := E) (extChartAt I x).target i
              (v i) y₀) =
          u y₀ *
            ∑ i : Fin (Module.finrank ℝ E),
              partialDerivWithin (E := E) (extChartAt I x).target i (v i) y₀ from
        (Finset.mul_sum _ _ _).symm]
  rw [add_div]
  have hsymm_inv : (extChartAt I x).symm y₀ = x := (extChartAt I x).left_inv hxsrc
  have hu_eq_φ : u y₀ = φ x := by
    change scalarOnE (I := I) x φ y₀ = φ x
    exact scalarOnE_extChartAt (I := I) x φ hxsrc
  congr 1
  · rw [hu_eq_φ, mul_div_assoc]
  · have hρOnE : chartDensityOnE (I := I) g x y₀ = chartDensity (I := I) g x x := by
      change chartDensity (I := I) g x ((extChartAt I x).symm y₀) = _
      rw [hsymm_inv]
    have heach : ∀ i : Fin (Module.finrank ℝ E),
        v i y₀ *
          partialDerivWithin (E := E) (extChartAt I x).target i u y₀ =
          (chartCoeffOnE (I := I) x X i y₀ *
              partialDerivWithin (E := E) (extChartAt I x).target i u y₀) *
            chartDensity (I := I) g x x := by
      intro i
      change (chartCoeffOnE (I := I) x X i y₀ *
            chartDensityOnE (I := I) g x y₀) *
          partialDerivWithin (E := E) (extChartAt I x).target i u y₀ =
        (chartCoeffOnE (I := I) x X i y₀ *
            partialDerivWithin (E := E) (extChartAt I x).target i u y₀) *
          chartDensity (I := I) g x x
      rw [hρOnE]
      ring
    rw [show (∑ i : Fin (Module.finrank ℝ E),
              v i y₀ *
                partialDerivWithin (E := E) (extChartAt I x).target i u y₀) =
            ∑ i : Fin (Module.finrank ℝ E),
              (chartCoeffOnE (I := I) x X i y₀ *
                  partialDerivWithin (E := E) (extChartAt I x).target i u y₀) *
                chartDensity (I := I) g x x from
          Finset.sum_congr rfl (fun i _ => heach i)]
    rw [← Finset.sum_mul]
    rw [mul_div_assoc, div_self hρ_ne, mul_one]
    have hchartCoeff : ∀ i : Fin (Module.finrank ℝ E),
        chartCoeffOnE (I := I) x X i y₀ = chartCoeff (I := I) x X i x := by
      intro i
      change chartCoeff (I := I) x X i ((extChartAt I x).symm y₀) = _
      rw [hsymm_inv]
    have htsa := tangentSectionAction_chartLocal_within (I := I) (α := x) X
      (f := φ) hφ (mem_chart_source H x)
    rw [htsa]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [hchartCoeff i]

omit [InnerProductSpace ℝ E] in
theorem divergence_g_with_boundary_smoothSmul [T2Space M]
    (g : SmoothRiemannianMetric I M)
    (φ : M → ℝ) (hφ : ContMDiff I 𝓘(ℝ) ∞ φ)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ∀ x : M,
      divergence_g_with_boundary (I := I) g
        (smoothSmul
          (I := I) φ hφ X) x =
        φ x * divergence_g_with_boundary (I := I) g X x +
          tangentSectionAction (I := I) X φ x := by
  intro x
  rw [divergence_g_with_boundary_def, divergence_g_with_boundary_def]
  exact localDivergenceWithin_at_self_smoothSmul (I := I) g x φ hφ X

omit [InnerProductSpace ℝ E] in
theorem divergence_g_with_boundary_add [T2Space M]
    (g : SmoothRiemannianMetric I M)
    (X Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ∀ x : M,
      divergence_g_with_boundary (I := I) g (X + Y) x =
        divergence_g_with_boundary (I := I) g X x +
          divergence_g_with_boundary (I := I) g Y x := by
  intro x
  classical
  rw [divergence_g_with_boundary_def, divergence_g_with_boundary_def,
      divergence_g_with_boundary_def]
  rw [localDivergenceWithin_def, localDivergenceWithin_def, localDivergenceWithin_def]
  set y₀ : E := extChartAt I x x with hy₀_def
  have hxsrc : x ∈ (extChartAt I x).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]
    exact mem_chart_source H x
  have hy₀_target : y₀ ∈ (extChartAt I x).target :=
    (extChartAt I x).map_source hxsrc
  have huniq : UniqueDiffWithinAt ℝ (extChartAt I x).target y₀ :=
    uniqueDiffOn_extChartAt_target_apply (I := I) x hy₀_target
  have hchartCoeff_add : ∀ z ∈ (trivializationAt E (TangentSpace I) x).baseSet,
      ∀ i : Fin (Module.finrank ℝ E),
        chartCoeff (I := I) x (X + Y) i z =
          chartCoeff (I := I) x X i z + chartCoeff (I := I) x Y i z := by
    intro z hz i
    classical
    set T : Bundle.Trivialization E (π E (TangentSpace I : M → Type _)) :=
      trivializationAt E (TangentSpace I) x
    have hadd : (T ⟨z, (X + Y) z⟩).2 = (T ⟨z, X z⟩).2 + (T ⟨z, Y z⟩).2 := by
      have h := (T.linear ℝ hz).map_add (X z) (Y z)
      change (T ⟨z, X z + Y z⟩).2 = (T ⟨z, X z⟩).2 + (T ⟨z, Y z⟩).2
      exact h
    unfold chartCoeff
    rw [hadd, LinearEquiv.map_add, Finsupp.add_apply]
  have hchartCoeffOnE_add : ∀ y ∈ (extChartAt I x).target,
      ∀ i : Fin (Module.finrank ℝ E),
        chartCoeffOnE (I := I) x (X + Y) i y =
          chartCoeffOnE (I := I) x X i y + chartCoeffOnE (I := I) x Y i y := by
    intro y hy i
    have hsymm_src : (extChartAt I x).symm y ∈ (extChartAt I x).source :=
      (extChartAt I x).map_target hy
    have hsymm_chart : (extChartAt I x).symm y ∈ (chartAt H x).source := by
      rw [extChartAt_source_eq_chartAt_source (I := I)] at hsymm_src
      exact hsymm_src
    have hsymm_base : (extChartAt I x).symm y ∈
        (trivializationAt E (TangentSpace I) x).baseSet := by
      rw [trivializationAt_baseSet_eq_chartAt_source]
      exact hsymm_chart
    unfold chartCoeffOnE
    exact hchartCoeff_add ((extChartAt I x).symm y) hsymm_base i
  have hpartial_split : ∀ i : Fin (Module.finrank ℝ E),
      partialDerivWithin (E := E) (extChartAt I x).target i
        (fun y => chartCoeffOnE (I := I) x (X + Y) i y *
          chartDensityOnE (I := I) g x y) y₀ =
      partialDerivWithin (E := E) (extChartAt I x).target i
        (fun y => chartCoeffOnE (I := I) x X i y *
          chartDensityOnE (I := I) g x y) y₀ +
      partialDerivWithin (E := E) (extChartAt I x).target i
        (fun y => chartCoeffOnE (I := I) x Y i y *
          chartDensityOnE (I := I) g x y) y₀ := by
    intro i
    have hcongr : partialDerivWithin (E := E) (extChartAt I x).target i
        (fun y => chartCoeffOnE (I := I) x (X + Y) i y *
          chartDensityOnE (I := I) g x y) y₀ =
        partialDerivWithin (E := E) (extChartAt I x).target i
          (fun y =>
            chartCoeffOnE (I := I) x X i y * chartDensityOnE (I := I) g x y +
            chartCoeffOnE (I := I) x Y i y * chartDensityOnE (I := I) g x y) y₀ := by
      refine partialDerivWithin_congr_of_eqOn_of_mem ?_ hy₀_target
      intro y hy
      simp only []
      rw [hchartCoeffOnE_add y hy i]
      ring
    rw [hcongr]
    have hX_diff : DifferentiableWithinAt ℝ
        (fun y => chartCoeffOnE (I := I) x X i y *
          chartDensityOnE (I := I) g x y) (extChartAt I x).target y₀ :=
      chartCoeffOnE_mul_chartDensityOnE_differentiableWithinAt
        (I := I) g x X i hy₀_target
    have hY_diff : DifferentiableWithinAt ℝ
        (fun y => chartCoeffOnE (I := I) x Y i y *
          chartDensityOnE (I := I) g x y) (extChartAt I x).target y₀ :=
      chartCoeffOnE_mul_chartDensityOnE_differentiableWithinAt
        (I := I) g x Y i hy₀_target
    exact partialDerivWithin_add (s := (extChartAt I x).target) (y := y₀) (i := i)
      _ _ huniq hX_diff hY_diff
  rw [show (∑ i : Fin (Module.finrank ℝ E),
            partialDerivWithin (E := E) (extChartAt I x).target i
              (fun y => chartCoeffOnE (I := I) x (X + Y) i y *
                chartDensityOnE (I := I) g x y) y₀) =
          ∑ i : Fin (Module.finrank ℝ E),
            (partialDerivWithin (E := E) (extChartAt I x).target i
              (fun y => chartCoeffOnE (I := I) x X i y *
                chartDensityOnE (I := I) g x y) y₀ +
            partialDerivWithin (E := E) (extChartAt I x).target i
              (fun y => chartCoeffOnE (I := I) x Y i y *
                chartDensityOnE (I := I) g x y) y₀) from
        Finset.sum_congr rfl (fun i _ => hpartial_split i)]
  rw [Finset.sum_add_distrib, add_div]

omit [InnerProductSpace ℝ E] in
@[simp] theorem divergence_g_with_boundary_zero [T2Space M]
    (g : SmoothRiemannianMetric I M) :
    ∀ x : M, divergence_g_with_boundary (I := I) g
      (0 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x = 0 := by
  intro x
  classical
  rw [divergence_g_with_boundary_def, localDivergenceWithin_def]
  set y₀ : E := extChartAt I x x with hy₀_def
  have hxsrc : x ∈ (extChartAt I x).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]
    exact mem_chart_source H x
  have hy₀_target : y₀ ∈ (extChartAt I x).target :=
    (extChartAt I x).map_source hxsrc
  have hchartCoeff_zero : ∀ z ∈ (trivializationAt E (TangentSpace I) x).baseSet,
      ∀ i : Fin (Module.finrank ℝ E),
        chartCoeff (I := I) x
          (0 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) i z = 0 := by
    intro z hz i
    classical
    set T : Bundle.Trivialization E (π E (TangentSpace I : M → Type _)) :=
      trivializationAt E (TangentSpace I) x
    have h0 : (T ⟨z, (0 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) z⟩).2 = 0 := by
      have h := (T.linear ℝ hz).map_zero
      change (T ⟨z, (0 : TangentSpace I z)⟩).2 = 0
      exact h
    unfold chartCoeff
    rw [h0]
    simp
  have hchartCoeffOnE_zero : ∀ y ∈ (extChartAt I x).target,
      ∀ i : Fin (Module.finrank ℝ E),
        chartCoeffOnE (I := I) x
          (0 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) i y = 0 := by
    intro y hy i
    have hsymm_src : (extChartAt I x).symm y ∈ (extChartAt I x).source :=
      (extChartAt I x).map_target hy
    have hsymm_chart : (extChartAt I x).symm y ∈ (chartAt H x).source := by
      rw [extChartAt_source_eq_chartAt_source (I := I)] at hsymm_src
      exact hsymm_src
    have hsymm_base : (extChartAt I x).symm y ∈
        (trivializationAt E (TangentSpace I) x).baseSet := by
      rw [trivializationAt_baseSet_eq_chartAt_source]
      exact hsymm_chart
    unfold chartCoeffOnE
    exact hchartCoeff_zero _ hsymm_base i
  have hpartial_zero : ∀ i : Fin (Module.finrank ℝ E),
      partialDerivWithin (E := E) (extChartAt I x).target i
        (fun y => chartCoeffOnE (I := I) x
          (0 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) i y *
          chartDensityOnE (I := I) g x y) y₀ = 0 := by
    intro i
    have hcongr_zero :
        partialDerivWithin (E := E) (extChartAt I x).target i
          (fun y => chartCoeffOnE (I := I) x
            (0 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) i y *
            chartDensityOnE (I := I) g x y) y₀ =
        partialDerivWithin (E := E) (extChartAt I x).target i
          (fun _ : E => (0 : ℝ)) y₀ := by
      refine partialDerivWithin_congr_of_eqOn_of_mem ?_ hy₀_target
      intro y hy
      simp only []
      rw [hchartCoeffOnE_zero y hy i]
      ring
    rw [hcongr_zero]
    unfold partialDerivWithin
    have h_const_eq : (fun _ : E => (0 : ℝ)) = Function.const E (0 : ℝ) := rfl
    rw [h_const_eq, fderivWithin_const]
    rfl
  rw [show (∑ i : Fin (Module.finrank ℝ E),
            partialDerivWithin (E := E) (extChartAt I x).target i
              (fun y => chartCoeffOnE (I := I) x
                (0 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) i y *
                chartDensityOnE (I := I) g x y) y₀) = 0 from
        Finset.sum_eq_zero (fun i _ => hpartial_zero i)]
  rw [zero_div]

omit [InnerProductSpace ℝ E] in
theorem divergence_g_with_boundary_pou_tsum [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (ρ : SmoothPartitionOfUnity M I M univ)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ∀ x : M, divergence_g_with_boundary (I := I) g X x =
      ∑' α : M, divergence_g_with_boundary (I := I) g
        (smoothSmul
          (I := I) (ρ α : M → ℝ) (ρ α).contMDiff X) x := by
  intro x
  classical
  set S : Finset M := ρ.fintsupport x with hS_def
  have h_tsum_eq_sum :
      (∑' α : M, divergence_g_with_boundary (I := I) g
          (smoothSmul
            (I := I) (ρ α : M → ℝ) (ρ α).contMDiff X) x) =
        ∑ α ∈ S, divergence_g_with_boundary (I := I) g
          (smoothSmul
            (I := I) (ρ α : M → ℝ) (ρ α).contMDiff X) x := by
    refine tsum_eq_sum ?_
    intro α hα
    have hxnotin : x ∉ tsupport (ρ α : M → ℝ) := by
      intro h
      apply hα
      rw [ρ.mem_fintsupport_iff]
      exact h
    rw [divergence_g_with_boundary_smoothSmul (I := I) g
        (ρ α : M → ℝ) (ρ α).contMDiff X x]
    have hραx : (ρ α : M → ℝ) x = 0 := by
      by_contra hne
      exact hxnotin (subset_tsupport _ hne)
    have htsa_zero : tangentSectionAction (I := I) X (ρ α : M → ℝ) x = 0 := by
      unfold tangentSectionAction
      have h_open : IsOpen (tsupport (ρ α : M → ℝ))ᶜ :=
        (isClosed_tsupport _).isOpen_compl
      have hev : (ρ α : M → ℝ) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
        filter_upwards [h_open.mem_nhds hxnotin] with y hy
        by_contra hne
        exact hy (subset_tsupport _ hne)
      rw [Filter.EventuallyEq.mfderiv_eq hev, mfderiv_const]
      rfl
    rw [hραx, htsa_zero, zero_mul, add_zero]
  rw [h_tsum_eq_sum]
  have h_each : ∀ α ∈ S,
      divergence_g_with_boundary (I := I) g
        (smoothSmul
          (I := I) (ρ α : M → ℝ) (ρ α).contMDiff X) x =
        (ρ α : M → ℝ) x * divergence_g_with_boundary (I := I) g X x +
          tangentSectionAction (I := I) X (ρ α : M → ℝ) x := by
    intro α _
    exact divergence_g_with_boundary_smoothSmul (I := I) g
      (ρ α : M → ℝ) (ρ α).contMDiff X x
  rw [Finset.sum_congr rfl h_each]
  rw [Finset.sum_add_distrib]
  rw [show (∑ α ∈ S, (ρ α : M → ℝ) x *
              divergence_g_with_boundary (I := I) g X x) =
        (∑ α ∈ S, (ρ α : M → ℝ) x) *
          divergence_g_with_boundary (I := I) g X x from
      (Finset.sum_mul _ _ _).symm]
  rw [ρ.sum_finsupport' x (mem_univ x)
        (ρ.finsupport_subset_fintsupport x)]
  rw [one_mul]
  have hsum_action : ∑ α ∈ S,
      tangentSectionAction (I := I) X (ρ α : M → ℝ) x = 0 := by
    have hMDiff_each : ∀ α ∈ S,
        MDifferentiableAt I 𝓘(ℝ) ((ρ α : M → ℝ)) x :=
      fun α _ => (ρ α).contMDiff.mdifferentiable (by simp) x
    have hcomm := tangentSectionAction_finset_sum
      (I := I) X S (fun α => ((ρ α : M → ℝ))) x hMDiff_each
    rw [← hcomm]
    have h_finset_eq_one : (fun y : M => ∑ α ∈ S, (ρ α : M → ℝ) y) =ᶠ[𝓝 x]
        (fun _ : M => (1 : ℝ)) := by
      filter_upwards [ρ.eventually_finsupport_subset x] with y hy
      exact ρ.sum_finsupport' y (mem_univ y) hy
    unfold tangentSectionAction
    have h_fun_eq : (∑ α ∈ S, (ρ α : M → ℝ)) = fun y : M => ∑ α ∈ S, (ρ α : M → ℝ) y := by
      funext y
      rw [Finset.sum_apply]
    rw [h_fun_eq]
    rw [Filter.EventuallyEq.mfderiv_eq h_finset_eq_one]
    rw [mfderiv_const]
    rfl
  rw [hsum_action]
  ring

end WithBoundary
end DivergenceTheorem
end Integral
end DifferentialGeometry
