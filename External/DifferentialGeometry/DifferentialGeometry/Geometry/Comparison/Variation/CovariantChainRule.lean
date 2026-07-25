import DifferentialGeometry.Geometry.Connection.ParallelTransport.CovariantDerivativeAlong
import DifferentialGeometry.Geometry.Connection.LeviCivita.Defs


noncomputable section

open Set Function Filter Manifold Bundle
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace CovariantDerivativeAlong

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.AlongCurve

omit [NeZero (Module.finrank ℝ E)] in
private lemma christoffelCorrection_eq_chartChristoffelContraction
    (g : SmoothRiemannianMetric I M) (α x : M) (Y : E) (v : TangentSpace I x) :
    christoffelCorrection (I := I) g α x Y v =
      chartChristoffelContraction (I := I) g α (trivToE (I := I) α x v) Y
        (extChartAt I α x) := by
  classical
  rw [christoffelCorrection_apply, chartChristoffelContraction_def]
  set F : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → E :=
    fun i j k =>
      (chartChristoffel (I := I) g α i j k (extChartAt I α x) *
          (chartModelBasis E).repr (trivToE (I := I) α x v) i *
          (chartModelBasis E).repr Y j) • (chartModelBasis E) k with hF
  have hLHS :
      (∑ i, ∑ j, ∑ k,
          ((chartModelBasis E).repr (trivToE (I := I) α x v) i *
                (chartModelBasis E).repr Y j *
                chartChristoffel (I := I) g α i j k (extChartAt I α x)) •
            (chartModelBasis E) k)
        = ∑ i, ∑ j, ∑ k, F i j k := by
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ =>
      Finset.sum_congr rfl (fun k _ => ?_)))
    rw [hF]; congr 1; ring
  have hRHS :
      (∑ k,
          (∑ i, ∑ j,
              chartChristoffel (I := I) g α i j k (extChartAt I α x) *
                chartCoord (E := E) i (trivToE (I := I) α x v) *
                chartCoord (E := E) j Y) •
            (chartModelBasis E) k)
        = ∑ i, ∑ j, ∑ k, F i j k := by
    have hstep1 :
        (∑ k,
            (∑ i, ∑ j,
                chartChristoffel (I := I) g α i j k (extChartAt I α x) *
                  chartCoord (E := E) i (trivToE (I := I) α x v) *
                  chartCoord (E := E) j Y) •
              (chartModelBasis E) k)
          = ∑ k, ∑ i, ∑ j, F i j k := by
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [Finset.sum_smul]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.sum_smul]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [hF, chartCoord_def, chartCoord_def]
    rw [hstep1, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_comm]
  rw [hLHS, hRHS]

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma chartRepAt_restrict_eq_comp
    (γ : ℝ → M) (X : ∀ y : M, TangentSpace I y) (r₀ : ℝ) :
    chartRepAt (I := I) γ (fun r => X (γ r)) r₀ =
      chartE_section_repr (I := I) (γ r₀) X ∘ γ := by
  funext s
  rfl

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma deriv_chartE_repr_comp_curve_eq
    [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
    (γ : ℝ → M) (X : ∀ y : M, TangentSpace I y) (r₀ : ℝ)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ)
    (hX : MDiffAt (T% X) (γ r₀)) :
    deriv (chartE_section_repr (I := I) (γ r₀) X ∘ γ) r₀ =
      fderiv ℝ (chartE_section_repr (I := I) (γ r₀) X ∘ (extChartAt I (γ r₀)).symm)
          (extChartAt I (γ r₀) (γ r₀))
        (deriv (chartCurve (I := I) (γ r₀) γ) r₀) := by
  classical
  set α : M := γ r₀ with hα_def
  set f : E → E := chartE_section_repr (I := I) α X ∘ (extChartAt I α).symm with hf_def
  set u : ℝ → E := chartCurve (I := I) α γ with hu_def
  have hgood : α ∈ chartLeviCivitaGoodSet (I := I) α :=
    self_mem_chartLeviCivitaGoodSet (I := I) (α := α)
  have hf_diff : DifferentiableAt ℝ f (extChartAt I α (γ r₀)) :=
    differentiableAt_chartE_pullback_of_MDiff (I := I) α hgood hX
  have hu_hd : HasDerivAt u (deriv u r₀) r₀ :=
    ((contDiffAt_chartCurve (I := I) hγ r₀).differentiableAt (by simp)).hasDerivAt
  have hxu : u r₀ = extChartAt I α (γ r₀) := by rw [hu_def, chartCurve_def]
  have hcomp_hd : HasDerivAt (f ∘ u) (fderiv ℝ f (extChartAt I α (γ r₀)) (deriv u r₀)) r₀ := by
    have hf_hd : HasFDerivAt f (fderiv ℝ f (extChartAt I α (γ r₀))) (u r₀) := by
      rw [hxu]; exact hf_diff.hasFDerivAt
    exact hf_hd.comp_hasDerivAt r₀ hu_hd
  have hsrc_nhds : γ ⁻¹' (extChartAt I α).source ∈ 𝓝 r₀ := by
    have hopen : IsOpen (extChartAt I α).source := isOpen_extChartAt_source (I := I) α
    have hmem : γ r₀ ∈ (extChartAt I α).source := by
      rw [extChartAt_source]; exact mem_chart_source H (γ r₀)
    exact hγ.continuous.continuousAt.preimage_mem_nhds (hopen.mem_nhds hmem)
  have heq : (f ∘ u) =ᶠ[𝓝 r₀] chartE_section_repr (I := I) α X ∘ γ := by
    filter_upwards [hsrc_nhds] with s hs
    have hs' : γ s ∈ (extChartAt I α).source := hs
    simp only [Function.comp_apply, hf_def, hu_def, chartCurve_def]
    rw [PartialEquiv.left_inv (extChartAt I α) hs']
  rw [← heq.deriv_eq]
  exact hcomp_hd.deriv

omit [NeZero (Module.finrank ℝ E)] in
theorem covDerivAlong_restrict_eq_leviCivita
    [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M) (X : ∀ y : M, TangentSpace I y) (r₀ : ℝ)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ)
    (hX : MDiffAt (T% X) (γ r₀)) :
    covDerivAlong (I := I) g γ (fun r => X (γ r)) r₀ =
      (LeviCivita (I := I) g) X (γ r₀) ((mfderiv 𝓘(ℝ, ℝ) I γ r₀ : ℝ →L[ℝ] _) (1 : ℝ)) := by
  classical
  set α : M := γ r₀ with hα_def
  set v : TangentSpace I α := (mfderiv 𝓘(ℝ, ℝ) I γ r₀ : ℝ →L[ℝ] _) (1 : ℝ) with hv_def
  have hgood : α ∈ chartLeviCivitaGoodSet (I := I) α :=
    self_mem_chartLeviCivitaGoodSet (I := I) (α := α)
  have hsrc : α ∈ (chartAt H α).source := mem_chart_source H α
  have hvel : trivToE (I := I) α α v = deriv (chartCurve (I := I) α γ) r₀ := by
    have hbridge := MFDerivAlongCurve.chartCoord_mfderiv_along_curve_eq_fderiv
      (I := I) (M := M) (γ := γ) hγ α (t := r₀) hsrc
    rw [trivToE]
    rw [show v = (mfderiv 𝓘(ℝ, ℝ) I γ r₀ : ℝ →L[ℝ] _) (1 : ℝ) from rfl]
    rw [hbridge]
    rw [show (extChartAt I α ∘ γ) = chartCurve (I := I) α γ from rfl]
    exact fderiv_apply_one_eq_deriv
  have hXmd : MDiffAt (T% (fun y => X y)) α := hX
  rw [show (LeviCivita (I := I) g) X (γ r₀) ((mfderiv 𝓘(ℝ, ℝ) I γ r₀ : ℝ →L[ℝ] _) (1 : ℝ))
        = (LeviCivita (I := I) g).toFun X α v from rfl]
  rw [LeviCivita_chart_apply (I := I) g α hgood hXmd v]
  rw [chartLeviCivita_apply (I := I) g α X hgood v]
  rw [covDerivAlong_def, chartCovDerivAlong_def]
  rw [chartRepAt_restrict_eq_comp (I := I) γ X r₀]
  rw [show (trivializationAt E (TangentSpace I) α).symmL ℝ α = trivFromE (I := I) α α from rfl]
  congr 1
  have hchris :
      chartChristoffelContraction (I := I) g α
          (deriv (chartCurve (I := I) α γ) r₀)
          ((chartE_section_repr (I := I) α X ∘ γ) r₀)
          (chartCurve (I := I) α γ r₀)
        = christoffelCorrection (I := I) g α α
            (chartE_section_repr (I := I) α X α) v := by
    rw [christoffelCorrection_eq_chartChristoffelContraction (I := I) g α α
      (chartE_section_repr (I := I) α X α) v]
    rw [hvel]
    rw [Function.comp_apply, ← hα_def, chartCurve_def, ← hα_def]
  have hderiv :
      deriv (chartE_section_repr (I := I) α X ∘ γ) r₀ =
        fderiv ℝ (chartE_section_repr (I := I) α X ∘ (extChartAt I α).symm)
            (extChartAt I α α) (trivToE (I := I) α α v) := by
    rw [hvel]
    exact deriv_chartE_repr_comp_curve_eq (I := I) γ X r₀ hγ hX
  rw [hderiv, hchris]

end CovariantDerivativeAlong

end Riemannian
end Geometry
end DifferentialGeometry

end
