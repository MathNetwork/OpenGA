import DifferentialGeometry.Analysis.Elliptic.Regularity.ChartBilinear.H1Compl


noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace DiffChartBilinearH1Compl

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

def weightedInvGramDerivOnEuclid (g : SmoothRiemannianMetric I M) (α : M)
    (i j l : Fin (Module.finrank ℝ E)) (y : EuclN) : ℝ :=
  (fderiv ℝ (weightedInvGramOnEuclid (I := I) g α i j) y)
    (EuclideanSpace.single l 1)

def densityDerivOnEuclid (g : SmoothRiemannianMetric I M) (α : M)
    (l : Fin (Module.finrank ℝ E)) (y : EuclN) : ℝ :=
  (fderiv ℝ (densityOnEuclid (I := I) g α) y) (EuclideanSpace.single l 1)

omit [NeZero (Module.finrank ℝ E)] in
lemma weightedInvGramDerivOnEuclid_contDiffOn
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j l : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (weightedInvGramDerivOnEuclid (I := I) g α i j l)
      (chartTargetEuclid (I := I) (M := M) α) := by
  have h_smooth :
      ContDiffOn ℝ ∞ (weightedInvGramOnEuclid (I := I) g α i j)
        (chartTargetEuclid (I := I) (M := M) α) :=
    weightedInvGramOnEuclid_contDiffOn (I := I) g α i j
  have h_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have h_fderiv :
      ContDiffOn ℝ ∞ (fun y => fderiv ℝ
        (weightedInvGramOnEuclid (I := I) g α i j) y)
        (chartTargetEuclid (I := I) (M := M) α) :=
    ((contDiffOn_infty_iff_fderiv_of_isOpen h_open).1 h_smooth).2
  have h_eval : ContDiff ℝ ∞
      (fun (L : EuclN →L[ℝ] ℝ) => L (EuclideanSpace.single l 1)) :=
    (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single l (1 : ℝ))).contDiff
  exact h_eval.contDiffOn.comp h_fderiv (mapsTo_univ _ _)

omit [NeZero (Module.finrank ℝ E)] in
lemma densityDerivOnEuclid_contDiffOn
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    (l : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (densityDerivOnEuclid (I := I) g α l)
      (chartTargetEuclid (I := I) (M := M) α) := by
  have h_smooth :
      ContDiffOn ℝ ∞ (densityOnEuclid (I := I) g α)
        (chartTargetEuclid (I := I) (M := M) α) :=
    densityOnEuclid_contDiffOn (I := I) g α
  have h_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have h_fderiv :
      ContDiffOn ℝ ∞ (fun y => fderiv ℝ (densityOnEuclid (I := I) g α) y)
        (chartTargetEuclid (I := I) (M := M) α) :=
    ((contDiffOn_infty_iff_fderiv_of_isOpen h_open).1 h_smooth).2
  have h_eval : ContDiff ℝ ∞
      (fun (L : EuclN →L[ℝ] ℝ) => L (EuclideanSpace.single l 1)) :=
    (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single l (1 : ℝ))).contDiff
  exact h_eval.contDiffOn.comp h_fderiv (mapsTo_univ _ _)

omit [NeZero (Module.finrank ℝ E)] in
lemma weightedInvGramDerivOnEuclid_continuousOn
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j l : Fin (Module.finrank ℝ E)) :
    ContinuousOn (weightedInvGramDerivOnEuclid (I := I) g α i j l)
      (chartTargetEuclid (I := I) (M := M) α) :=
  (weightedInvGramDerivOnEuclid_contDiffOn (I := I) g α i j l).continuousOn

omit [NeZero (Module.finrank ℝ E)] in
lemma densityDerivOnEuclid_continuousOn
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    (l : Fin (Module.finrank ℝ E)) :
    ContinuousOn (densityDerivOnEuclid (I := I) g α l)
      (chartTargetEuclid (I := I) (M := M) α) :=
  (densityDerivOnEuclid_contDiffOn (I := I) g α l).continuousOn

omit [NeZero (Module.finrank ℝ E)] in
lemma weightedInvGramDerivOnEuclid_bounded_on_compact
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j l : Fin (Module.finrank ℝ E))
    {K : Set EuclN} (hK_compact : IsCompact K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ∃ C : ℝ, ∀ y ∈ K,
      |weightedInvGramDerivOnEuclid (I := I) g α i j l y| ≤ C := by
  classical
  by_cases hK_empty : K = ∅
  · refine ⟨0, ?_⟩
    intro y hy
    rw [hK_empty] at hy
    exact absurd hy (Set.notMem_empty y)
  have h_K_ne : K.Nonempty := Set.nonempty_iff_ne_empty.mpr hK_empty
  have h_cont_K : ContinuousOn
      (weightedInvGramDerivOnEuclid (I := I) g α i j l) K :=
    (weightedInvGramDerivOnEuclid_continuousOn (I := I) g α i j l).mono hK_in
  have h_abs_K : ContinuousOn
      (fun y => |weightedInvGramDerivOnEuclid (I := I) g α i j l y|) K :=
    continuous_abs.comp_continuousOn h_cont_K
  obtain ⟨y_max, hy_max, h_max⟩ :=
    hK_compact.exists_isMaxOn h_K_ne h_abs_K
  refine ⟨|weightedInvGramDerivOnEuclid (I := I) g α i j l y_max|, ?_⟩
  intro y hy
  exact h_max hy

omit [NeZero (Module.finrank ℝ E)] in
lemma densityDerivOnEuclid_bounded_on_compact
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    (l : Fin (Module.finrank ℝ E))
    {K : Set EuclN} (hK_compact : IsCompact K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ∃ C : ℝ, ∀ y ∈ K, |densityDerivOnEuclid (I := I) g α l y| ≤ C := by
  classical
  by_cases hK_empty : K = ∅
  · refine ⟨0, ?_⟩
    intro y hy
    rw [hK_empty] at hy
    exact absurd hy (Set.notMem_empty y)
  have h_K_ne : K.Nonempty := Set.nonempty_iff_ne_empty.mpr hK_empty
  have h_cont_K : ContinuousOn (densityDerivOnEuclid (I := I) g α l) K :=
    (densityDerivOnEuclid_continuousOn (I := I) g α l).mono hK_in
  have h_abs_K : ContinuousOn
      (fun y => |densityDerivOnEuclid (I := I) g α l y|) K :=
    continuous_abs.comp_continuousOn h_cont_K
  obtain ⟨y_max, hy_max, h_max⟩ :=
    hK_compact.exists_isMaxOn h_K_ne h_abs_K
  refine ⟨|densityDerivOnEuclid (I := I) g α l y_max|, ?_⟩
  intro y hy
  exact h_max hy

structure DiffChartBilinearH1ComplData
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M) where

  base : ChartBilinearH1ComplData (I := I) (M := M) g α

  direction : Fin (Module.finrank ℝ E)

  u_chart_deriv : EuclN → ℝ

  f_chart_deriv : EuclN → ℝ

  weak_partial_deriv : Fin (Module.finrank ℝ E) → EuclN → ℝ

  u_chart_deriv_isWeakPartial :
    DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) direction
      u_chart_deriv base.u_chart
      (chartTargetEuclid (I := I) (M := M) α)

  f_chart_deriv_isWeakPartial :
    DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) direction
      f_chart_deriv base.f_chart
      (chartTargetEuclid (I := I) (M := M) α)

  weak_partial_deriv_isWeakPartial :
    ∀ i, DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) direction
      (weak_partial_deriv i) (base.weak_partial i)
      (chartTargetEuclid (I := I) (M := M) α)

  u_chart_deriv_locally_memLp :
    ∀ K : Set EuclN, IsCompact K →
      K ⊆ chartTargetEuclid (I := I) (M := M) α →
      MemLp u_chart_deriv 2 ((volume : Measure EuclN).restrict K)

  f_chart_deriv_locally_memLp :
    ∀ K : Set EuclN, IsCompact K →
      K ⊆ chartTargetEuclid (I := I) (M := M) α →
      MemLp f_chart_deriv 2 ((volume : Measure EuclN).restrict K)

  weak_partial_deriv_locally_memLp :
    ∀ i, ∀ K : Set EuclN, IsCompact K →
      K ⊆ chartTargetEuclid (I := I) (M := M) α →
      MemLp (weak_partial_deriv i) 2
        ((volume : Measure EuclN).restrict K)

  differentiated_variational_identity :
    ∀ ψ : EuclN → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α →
      (∫ y in chartTargetEuclid (I := I) (M := M) α,
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            weightedInvGramOnEuclid (I := I) g α i j y *
              weak_partial_deriv i y *
              (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
        ∂(volume : Measure EuclN)) +
      (∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y * u_chart_deriv y * ψ y
        ∂(volume : Measure EuclN)) =
      (∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y * f_chart_deriv y * ψ y
        ∂(volume : Measure EuclN)) -
      (∫ y in chartTargetEuclid (I := I) (M := M) α,
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            weightedInvGramDerivOnEuclid (I := I) g α i j direction y *
              base.weak_partial i y *
              (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
        ∂(volume : Measure EuclN)) -
      (∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityDerivOnEuclid (I := I) g α direction y *
          base.u_chart y * ψ y
        ∂(volume : Measure EuclN)) +
      (∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityDerivOnEuclid (I := I) g α direction y *
          base.f_chart y * ψ y
        ∂(volume : Measure EuclN))

omit [NeZero (Module.finrank ℝ E)] in
theorem differentiated_chart_bilinear_identity
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : DiffChartBilinearH1ComplData (I := I) (M := M) g α)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          weightedInvGramOnEuclid (I := I) g α i j y *
            D.weak_partial_deriv i y *
            (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
      ∂(volume : Measure EuclN)) +
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      densityOnEuclid (I := I) g α y * D.u_chart_deriv y * ψ y
      ∂(volume : Measure EuclN)) =
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      densityOnEuclid (I := I) g α y * D.f_chart_deriv y * ψ y
      ∂(volume : Measure EuclN)) -
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          weightedInvGramDerivOnEuclid (I := I) g α i j D.direction y *
            D.base.weak_partial i y *
            (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
      ∂(volume : Measure EuclN)) -
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      densityDerivOnEuclid (I := I) g α D.direction y *
        D.base.u_chart y * ψ y
      ∂(volume : Measure EuclN)) +
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      densityDerivOnEuclid (I := I) g α D.direction y *
        D.base.f_chart y * ψ y
      ∂(volume : Measure EuclN)) :=
  D.differentiated_variational_identity ψ hψ hψ_cs hψ_supp

abbrev base
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : DiffChartBilinearH1ComplData (I := I) (M := M) g α) :
    ChartBilinearH1ComplData (I := I) (M := M) g α := D.base

abbrev direction
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : DiffChartBilinearH1ComplData (I := I) (M := M) g α) :
    Fin (Module.finrank ℝ E) := D.direction

omit [NeZero (Module.finrank ℝ E)] in
theorem base_chart_bilinear_identity
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : DiffChartBilinearH1ComplData (I := I) (M := M) g α)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          weightedInvGramOnEuclid (I := I) g α i j y *
            D.base.weak_partial i y *
            (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
      ∂(volume : Measure EuclN)) +
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      densityOnEuclid (I := I) g α y * D.base.u_chart y * ψ y
      ∂(volume : Measure EuclN)) =
    ∫ y in chartTargetEuclid (I := I) (M := M) α,
      densityOnEuclid (I := I) g α y * D.base.f_chart y * ψ y
      ∂(volume : Measure EuclN) :=
  D.base.variational_identity ψ hψ hψ_cs hψ_supp

end DiffChartBilinearH1Compl
end Laplacian
end Analysis
end DifferentialGeometry
