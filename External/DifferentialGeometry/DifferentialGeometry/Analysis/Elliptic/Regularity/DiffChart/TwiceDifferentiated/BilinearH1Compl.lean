import DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.Differentiated.BilinearH1Compl
import DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.ResidualRegularity.BilinearH1ComplFromDomainPow
import DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolevSpace.IteratedSobolev


noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace DiffTwiceChartBilinearH1Compl

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainChartData
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

def weightedInvGramSecondDerivOnEuclid (g : SmoothRiemannianMetric I M) (α : M)
    (i j l₁ l₂ : Fin (Module.finrank ℝ E)) (y : EuclN) : ℝ :=
  (fderiv ℝ
      (weightedInvGramDerivOnEuclid (I := I) g α i j l₁) y)
    (EuclideanSpace.single l₂ 1)

def densitySecondDerivOnEuclid (g : SmoothRiemannianMetric I M) (α : M)
    (l₁ l₂ : Fin (Module.finrank ℝ E)) (y : EuclN) : ℝ :=
  (fderiv ℝ (densityDerivOnEuclid (I := I) g α l₁) y)
    (EuclideanSpace.single l₂ 1)

omit [NeZero (Module.finrank ℝ E)] in
lemma weightedInvGramSecondDerivOnEuclid_contDiffOn
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j l₁ l₂ : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (weightedInvGramSecondDerivOnEuclid (I := I) g α i j l₁ l₂)
      (chartTargetEuclid (I := I) (M := M) α) := by
  have h_smooth :
      ContDiffOn ℝ ∞ (weightedInvGramDerivOnEuclid (I := I) g α i j l₁)
        (chartTargetEuclid (I := I) (M := M) α) :=
    weightedInvGramDerivOnEuclid_contDiffOn (I := I) g α i j l₁
  have h_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have h_fderiv :
      ContDiffOn ℝ ∞ (fun y => fderiv ℝ
        (weightedInvGramDerivOnEuclid (I := I) g α i j l₁) y)
        (chartTargetEuclid (I := I) (M := M) α) :=
    ((contDiffOn_infty_iff_fderiv_of_isOpen h_open).1 h_smooth).2
  have h_eval : ContDiff ℝ ∞
      (fun (L : EuclN →L[ℝ] ℝ) => L (EuclideanSpace.single l₂ 1)) :=
    (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single l₂ (1 : ℝ))).contDiff
  exact h_eval.contDiffOn.comp h_fderiv (mapsTo_univ _ _)

omit [NeZero (Module.finrank ℝ E)] in
lemma densitySecondDerivOnEuclid_contDiffOn
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    (l₁ l₂ : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (densitySecondDerivOnEuclid (I := I) g α l₁ l₂)
      (chartTargetEuclid (I := I) (M := M) α) := by
  have h_smooth :
      ContDiffOn ℝ ∞ (densityDerivOnEuclid (I := I) g α l₁)
        (chartTargetEuclid (I := I) (M := M) α) :=
    densityDerivOnEuclid_contDiffOn (I := I) g α l₁
  have h_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have h_fderiv :
      ContDiffOn ℝ ∞ (fun y => fderiv ℝ
        (densityDerivOnEuclid (I := I) g α l₁) y)
        (chartTargetEuclid (I := I) (M := M) α) :=
    ((contDiffOn_infty_iff_fderiv_of_isOpen h_open).1 h_smooth).2
  have h_eval : ContDiff ℝ ∞
      (fun (L : EuclN →L[ℝ] ℝ) => L (EuclideanSpace.single l₂ 1)) :=
    (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single l₂ (1 : ℝ))).contDiff
  exact h_eval.contDiffOn.comp h_fderiv (mapsTo_univ _ _)

omit [NeZero (Module.finrank ℝ E)] in
lemma weightedInvGramSecondDerivOnEuclid_continuousOn
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j l₁ l₂ : Fin (Module.finrank ℝ E)) :
    ContinuousOn (weightedInvGramSecondDerivOnEuclid (I := I) g α i j l₁ l₂)
      (chartTargetEuclid (I := I) (M := M) α) :=
  (weightedInvGramSecondDerivOnEuclid_contDiffOn (I := I) g α i j l₁ l₂).continuousOn

omit [NeZero (Module.finrank ℝ E)] in
lemma densitySecondDerivOnEuclid_continuousOn
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    (l₁ l₂ : Fin (Module.finrank ℝ E)) :
    ContinuousOn (densitySecondDerivOnEuclid (I := I) g α l₁ l₂)
      (chartTargetEuclid (I := I) (M := M) α) :=
  (densitySecondDerivOnEuclid_contDiffOn (I := I) g α l₁ l₂).continuousOn

omit [NeZero (Module.finrank ℝ E)] in
lemma weightedInvGramSecondDerivOnEuclid_bounded_on_compact
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j l₁ l₂ : Fin (Module.finrank ℝ E))
    {K : Set EuclN} (hK_compact : IsCompact K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ∃ C : ℝ, ∀ y ∈ K,
      |weightedInvGramSecondDerivOnEuclid (I := I) g α i j l₁ l₂ y| ≤ C := by
  classical
  by_cases hK_empty : K = ∅
  · refine ⟨0, ?_⟩
    intro y hy
    rw [hK_empty] at hy
    exact absurd hy (Set.notMem_empty y)
  have h_K_ne : K.Nonempty := Set.nonempty_iff_ne_empty.mpr hK_empty
  have h_cont_K : ContinuousOn
      (weightedInvGramSecondDerivOnEuclid (I := I) g α i j l₁ l₂) K :=
    (weightedInvGramSecondDerivOnEuclid_continuousOn (I := I) g α i j l₁ l₂).mono hK_in
  have h_abs_K : ContinuousOn
      (fun y => |weightedInvGramSecondDerivOnEuclid (I := I) g α i j l₁ l₂ y|) K :=
    continuous_abs.comp_continuousOn h_cont_K
  obtain ⟨y_max, hy_max, h_max⟩ :=
    hK_compact.exists_isMaxOn h_K_ne h_abs_K
  refine ⟨|weightedInvGramSecondDerivOnEuclid (I := I) g α i j l₁ l₂ y_max|, ?_⟩
  intro y hy
  exact h_max hy

omit [NeZero (Module.finrank ℝ E)] in
lemma densitySecondDerivOnEuclid_bounded_on_compact
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    (l₁ l₂ : Fin (Module.finrank ℝ E))
    {K : Set EuclN} (hK_compact : IsCompact K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ∃ C : ℝ, ∀ y ∈ K, |densitySecondDerivOnEuclid (I := I) g α l₁ l₂ y| ≤ C := by
  classical
  by_cases hK_empty : K = ∅
  · refine ⟨0, ?_⟩
    intro y hy
    rw [hK_empty] at hy
    exact absurd hy (Set.notMem_empty y)
  have h_K_ne : K.Nonempty := Set.nonempty_iff_ne_empty.mpr hK_empty
  have h_cont_K : ContinuousOn (densitySecondDerivOnEuclid (I := I) g α l₁ l₂) K :=
    (densitySecondDerivOnEuclid_continuousOn (I := I) g α l₁ l₂).mono hK_in
  have h_abs_K : ContinuousOn
      (fun y => |densitySecondDerivOnEuclid (I := I) g α l₁ l₂ y|) K :=
    continuous_abs.comp_continuousOn h_cont_K
  obtain ⟨y_max, hy_max, h_max⟩ :=
    hK_compact.exists_isMaxOn h_K_ne h_abs_K
  refine ⟨|densitySecondDerivOnEuclid (I := I) g α l₁ l₂ y_max|, ?_⟩
  intro y hy
  exact h_max hy

structure DiffTwiceChartBilinearH1ComplData
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M) where

  base1 : DiffChartBilinearH1ComplData (I := I) (M := M) g α

  direction2 : Fin (Module.finrank ℝ E)

  u_chart_deriv2 : EuclN → ℝ

  f_chart_deriv2 : EuclN → ℝ

  u_chart_second_deriv : EuclN → ℝ

  weak_partial_deriv2 : Fin (Module.finrank ℝ E) → EuclN → ℝ

  weak_partial_second_deriv : Fin (Module.finrank ℝ E) → EuclN → ℝ

  u_chart_deriv2_isWeakPartial :
    DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) direction2
      u_chart_deriv2 base1.u_chart_deriv
      (chartTargetEuclid (I := I) (M := M) α)

  f_chart_deriv2_isWeakPartial :
    DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) direction2
      f_chart_deriv2 base1.f_chart_deriv
      (chartTargetEuclid (I := I) (M := M) α)

  u_chart_second_deriv_isWeakPartial :
    DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) direction2
      u_chart_second_deriv base1.u_chart_deriv
      (chartTargetEuclid (I := I) (M := M) α)

  weak_partial_deriv2_isWeakPartial :
    ∀ i, DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) direction2
      (weak_partial_deriv2 i) (base1.weak_partial_deriv i)
      (chartTargetEuclid (I := I) (M := M) α)

  weak_partial_second_deriv_isWeakPartial :
    ∀ i, DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) direction2
      (weak_partial_second_deriv i) (base1.weak_partial_deriv i)
      (chartTargetEuclid (I := I) (M := M) α)

  u_chart_deriv2_locally_memLp :
    ∀ K : Set EuclN, IsCompact K →
      K ⊆ chartTargetEuclid (I := I) (M := M) α →
      MemLp u_chart_deriv2 2 ((volume : Measure EuclN).restrict K)

  f_chart_deriv2_locally_memLp :
    ∀ K : Set EuclN, IsCompact K →
      K ⊆ chartTargetEuclid (I := I) (M := M) α →
      MemLp f_chart_deriv2 2 ((volume : Measure EuclN).restrict K)

  u_chart_second_deriv_locally_memLp :
    ∀ K : Set EuclN, IsCompact K →
      K ⊆ chartTargetEuclid (I := I) (M := M) α →
      MemLp u_chart_second_deriv 2 ((volume : Measure EuclN).restrict K)

  weak_partial_deriv2_locally_memLp :
    ∀ i, ∀ K : Set EuclN, IsCompact K →
      K ⊆ chartTargetEuclid (I := I) (M := M) α →
      MemLp (weak_partial_deriv2 i) 2
        ((volume : Measure EuclN).restrict K)

  weak_partial_second_deriv_locally_memLp :
    ∀ i, ∀ K : Set EuclN, IsCompact K →
      K ⊆ chartTargetEuclid (I := I) (M := M) α →
      MemLp (weak_partial_second_deriv i) 2
        ((volume : Measure EuclN).restrict K)

  twice_differentiated_variational_identity :
    ∀ ψ : EuclN → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α →
      (∫ y in chartTargetEuclid (I := I) (M := M) α,
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            weightedInvGramOnEuclid (I := I) g α i j y *
              weak_partial_second_deriv i y *
              (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
        ∂(volume : Measure EuclN)) +
      (∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y * u_chart_second_deriv y * ψ y
        ∂(volume : Measure EuclN)) =
      (∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y * f_chart_deriv2 y * ψ y
        ∂(volume : Measure EuclN)) -
      (∫ y in chartTargetEuclid (I := I) (M := M) α,
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            weightedInvGramDerivOnEuclid (I := I) g α i j direction2 y *
              weak_partial_deriv2 i y *
              (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
        ∂(volume : Measure EuclN)) -
      (∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityDerivOnEuclid (I := I) g α direction2 y *
          u_chart_deriv2 y * ψ y
        ∂(volume : Measure EuclN)) +
      (∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityDerivOnEuclid (I := I) g α direction2 y *
          f_chart_deriv2 y * ψ y
        ∂(volume : Measure EuclN)) -
      (∫ y in chartTargetEuclid (I := I) (M := M) α,
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            weightedInvGramDerivOnEuclid (I := I) g α i j base1.direction y *
              weak_partial_deriv2 i y *
              (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
        ∂(volume : Measure EuclN)) -
      (∫ y in chartTargetEuclid (I := I) (M := M) α,
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            weightedInvGramSecondDerivOnEuclid (I := I) g α i j
                base1.direction direction2 y *
              base1.base.weak_partial i y *
              (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
        ∂(volume : Measure EuclN)) -
      (∫ y in chartTargetEuclid (I := I) (M := M) α,
        densitySecondDerivOnEuclid (I := I) g α
            base1.direction direction2 y *
          base1.base.u_chart y * ψ y
        ∂(volume : Measure EuclN)) -
      (∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityDerivOnEuclid (I := I) g α base1.direction y *
          base1.base.weak_partial direction2 y * ψ y
        ∂(volume : Measure EuclN)) +
      (∫ y in chartTargetEuclid (I := I) (M := M) α,
        densitySecondDerivOnEuclid (I := I) g α
            base1.direction direction2 y *
          base1.base.f_chart y * ψ y
        ∂(volume : Measure EuclN)) +
      (∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityDerivOnEuclid (I := I) g α base1.direction y *
          f_chart_deriv2 y * ψ y
        ∂(volume : Measure EuclN))

abbrev base1Data
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : DiffTwiceChartBilinearH1ComplData (I := I) (M := M) g α) :
    DiffChartBilinearH1ComplData (I := I) (M := M) g α := D.base1

abbrev baseData
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : DiffTwiceChartBilinearH1ComplData (I := I) (M := M) g α) :
    ChartBilinearH1ComplData (I := I) (M := M) g α := D.base1.base

abbrev direction1
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : DiffTwiceChartBilinearH1ComplData (I := I) (M := M) g α) :
    Fin (Module.finrank ℝ E) := D.base1.direction

omit [NeZero (Module.finrank ℝ E)] in
theorem twice_differentiated_chart_bilinear_identity
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : DiffTwiceChartBilinearH1ComplData (I := I) (M := M) g α)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          weightedInvGramOnEuclid (I := I) g α i j y *
            D.weak_partial_second_deriv i y *
            (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
      ∂(volume : Measure EuclN)) +
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      densityOnEuclid (I := I) g α y * D.u_chart_second_deriv y * ψ y
      ∂(volume : Measure EuclN)) =
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      densityOnEuclid (I := I) g α y * D.f_chart_deriv2 y * ψ y
      ∂(volume : Measure EuclN)) -
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          weightedInvGramDerivOnEuclid (I := I) g α i j D.direction2 y *
            D.weak_partial_deriv2 i y *
            (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
      ∂(volume : Measure EuclN)) -
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      densityDerivOnEuclid (I := I) g α D.direction2 y *
        D.u_chart_deriv2 y * ψ y
      ∂(volume : Measure EuclN)) +
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      densityDerivOnEuclid (I := I) g α D.direction2 y *
        D.f_chart_deriv2 y * ψ y
      ∂(volume : Measure EuclN)) -
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          weightedInvGramDerivOnEuclid (I := I) g α i j D.base1.direction y *
            D.weak_partial_deriv2 i y *
            (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
      ∂(volume : Measure EuclN)) -
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          weightedInvGramSecondDerivOnEuclid (I := I) g α i j
              D.base1.direction D.direction2 y *
            D.base1.base.weak_partial i y *
            (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
      ∂(volume : Measure EuclN)) -
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      densitySecondDerivOnEuclid (I := I) g α
          D.base1.direction D.direction2 y *
        D.base1.base.u_chart y * ψ y
      ∂(volume : Measure EuclN)) -
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      densityDerivOnEuclid (I := I) g α D.base1.direction y *
        D.base1.base.weak_partial D.direction2 y * ψ y
      ∂(volume : Measure EuclN)) +
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      densitySecondDerivOnEuclid (I := I) g α
          D.base1.direction D.direction2 y *
        D.base1.base.f_chart y * ψ y
      ∂(volume : Measure EuclN)) +
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      densityDerivOnEuclid (I := I) g α D.base1.direction y *
        D.f_chart_deriv2 y * ψ y
      ∂(volume : Measure EuclN)) :=
  D.twice_differentiated_variational_identity ψ hψ hψ_cs hψ_supp

omit [NeZero (Module.finrank ℝ E)] in
theorem differentiated_chart_bilinear_identity_via_base1
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : DiffTwiceChartBilinearH1ComplData (I := I) (M := M) g α)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          weightedInvGramOnEuclid (I := I) g α i j y *
            D.base1.weak_partial_deriv i y *
            (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
      ∂(volume : Measure EuclN)) +
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      densityOnEuclid (I := I) g α y * D.base1.u_chart_deriv y * ψ y
      ∂(volume : Measure EuclN)) =
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      densityOnEuclid (I := I) g α y * D.base1.f_chart_deriv y * ψ y
      ∂(volume : Measure EuclN)) -
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          weightedInvGramDerivOnEuclid (I := I) g α i j D.base1.direction y *
            D.base1.base.weak_partial i y *
            (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
      ∂(volume : Measure EuclN)) -
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      densityDerivOnEuclid (I := I) g α D.base1.direction y *
        D.base1.base.u_chart y * ψ y
      ∂(volume : Measure EuclN)) +
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      densityDerivOnEuclid (I := I) g α D.base1.direction y *
        D.base1.base.f_chart y * ψ y
      ∂(volume : Measure EuclN)) :=
  D.base1.differentiated_variational_identity ψ hψ hψ_cs hψ_supp

omit [NeZero (Module.finrank ℝ E)] in
theorem base_chart_bilinear_identity_via_base1
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : DiffTwiceChartBilinearH1ComplData (I := I) (M := M) g α)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          weightedInvGramOnEuclid (I := I) g α i j y *
            D.base1.base.weak_partial i y *
            (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
      ∂(volume : Measure EuclN)) +
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      densityOnEuclid (I := I) g α y * D.base1.base.u_chart y * ψ y
      ∂(volume : Measure EuclN)) =
    ∫ y in chartTargetEuclid (I := I) (M := M) α,
      densityOnEuclid (I := I) g α y * D.base1.base.f_chart y * ψ y
      ∂(volume : Measure EuclN) :=
  D.base1.base.variational_identity ψ hψ hψ_cs hψ_supp

omit [NeZero (Module.finrank ℝ E)] in
theorem u_chart_second_deriv_isMixedWeakPartial
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : DiffTwiceChartBilinearH1ComplData (I := I) (M := M) g α) :
    DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) D.direction2
      D.u_chart_second_deriv D.base1.u_chart_deriv
      (chartTargetEuclid (I := I) (M := M) α) ∧
    DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) D.base1.direction
      D.base1.u_chart_deriv D.base1.base.u_chart
      (chartTargetEuclid (I := I) (M := M) α) :=
  ⟨D.u_chart_second_deriv_isWeakPartial,
   D.base1.u_chart_deriv_isWeakPartial⟩

omit [NeZero (Module.finrank ℝ E)] in
theorem weak_partial_second_deriv_isMixedWeakPartial
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : DiffTwiceChartBilinearH1ComplData (I := I) (M := M) g α)
    (i : Fin (Module.finrank ℝ E)) :
    DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) D.direction2
      (D.weak_partial_second_deriv i) (D.base1.weak_partial_deriv i)
      (chartTargetEuclid (I := I) (M := M) α) ∧
    DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) D.base1.direction
      (D.base1.weak_partial_deriv i) (D.base1.base.weak_partial i)
      (chartTargetEuclid (I := I) (M := M) α) :=
  ⟨D.weak_partial_second_deriv_isWeakPartial i,
   D.base1.weak_partial_deriv_isWeakPartial i⟩

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

noncomputable def chosenSecondPartialUChartDeriv
    {g : SmoothRiemannianMetric I M} {α : M}
    (D₁ : DiffChartBilinearH1ComplData (I := I) (M := M) g α)
    (l₂ : Fin (Module.finrank ℝ E)) : EuclN → ℝ :=
  DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
    (d := Module.finrank ℝ E) 2 l₂ D₁.u_chart_deriv
    (chartTargetEuclid (I := I) (M := M) α)

noncomputable def chosenSecondPartialFChartDeriv
    {g : SmoothRiemannianMetric I M} {α : M}
    (D₁ : DiffChartBilinearH1ComplData (I := I) (M := M) g α)
    (l₂ : Fin (Module.finrank ℝ E)) : EuclN → ℝ :=
  DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
    (d := Module.finrank ℝ E) 2 l₂ D₁.f_chart_deriv
    (chartTargetEuclid (I := I) (M := M) α)

noncomputable def chosenSecondPartialWeakPartialDeriv
    {g : SmoothRiemannianMetric I M} {α : M}
    (D₁ : DiffChartBilinearH1ComplData (I := I) (M := M) g α)
    (i l₂ : Fin (Module.finrank ℝ E)) : EuclN → ℝ :=
  DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
    (d := Module.finrank ℝ E) 2 l₂ (D₁.weak_partial_deriv i)
    (chartTargetEuclid (I := I) (M := M) α)

omit [NeZero (Module.finrank ℝ E)] in
private lemma chosenSecondPartialUChartDeriv_isWeakPartial
    {g : SmoothRiemannianMetric I M} {α : M}
    {D₁ : DiffChartBilinearH1ComplData (I := I) (M := M) g α}
    (h_memW1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      D₁.u_chart_deriv (chartTargetEuclid (I := I) (M := M) α))
    (l₂ : Fin (Module.finrank ℝ E)) :
    DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) l₂
      (chosenSecondPartialUChartDeriv (I := I) (M := M) D₁ l₂)
      D₁.u_chart_deriv
      (chartTargetEuclid (I := I) (M := M) α) := by
  unfold chosenSecondPartialUChartDeriv
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_isWeakPartial_of_mem
    h_memW1p l₂

omit [NeZero (Module.finrank ℝ E)] in
private lemma chosenSecondPartialFChartDeriv_isWeakPartial
    {g : SmoothRiemannianMetric I M} {α : M}
    {D₁ : DiffChartBilinearH1ComplData (I := I) (M := M) g α}
    (h_memW1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      D₁.f_chart_deriv (chartTargetEuclid (I := I) (M := M) α))
    (l₂ : Fin (Module.finrank ℝ E)) :
    DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) l₂
      (chosenSecondPartialFChartDeriv (I := I) (M := M) D₁ l₂)
      D₁.f_chart_deriv
      (chartTargetEuclid (I := I) (M := M) α) := by
  unfold chosenSecondPartialFChartDeriv
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_isWeakPartial_of_mem
    h_memW1p l₂

omit [NeZero (Module.finrank ℝ E)] in
private lemma chosenSecondPartialWeakPartialDeriv_isWeakPartial
    {g : SmoothRiemannianMetric I M} {α : M}
    {D₁ : DiffChartBilinearH1ComplData (I := I) (M := M) g α}
    {i : Fin (Module.finrank ℝ E)}
    (h_memW1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (D₁.weak_partial_deriv i) (chartTargetEuclid (I := I) (M := M) α))
    (l₂ : Fin (Module.finrank ℝ E)) :
    DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) l₂
      (chosenSecondPartialWeakPartialDeriv (I := I) (M := M) D₁ i l₂)
      (D₁.weak_partial_deriv i)
      (chartTargetEuclid (I := I) (M := M) α) := by
  unfold chosenSecondPartialWeakPartialDeriv
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_isWeakPartial_of_mem
    h_memW1p l₂

omit [NeZero (Module.finrank ℝ E)] in
private lemma chosenSecondPartialUChartDeriv_memLp
    {g : SmoothRiemannianMetric I M} {α : M}
    {D₁ : DiffChartBilinearH1ComplData (I := I) (M := M) g α}
    (h_memW1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      D₁.u_chart_deriv (chartTargetEuclid (I := I) (M := M) α))
    (l₂ : Fin (Module.finrank ℝ E)) :
    MemLp (chosenSecondPartialUChartDeriv (I := I) (M := M) D₁ l₂) 2
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  unfold chosenSecondPartialUChartDeriv
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_memLp_of_mem
    h_memW1p l₂

omit [NeZero (Module.finrank ℝ E)] in
private lemma chosenSecondPartialFChartDeriv_memLp
    {g : SmoothRiemannianMetric I M} {α : M}
    {D₁ : DiffChartBilinearH1ComplData (I := I) (M := M) g α}
    (h_memW1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      D₁.f_chart_deriv (chartTargetEuclid (I := I) (M := M) α))
    (l₂ : Fin (Module.finrank ℝ E)) :
    MemLp (chosenSecondPartialFChartDeriv (I := I) (M := M) D₁ l₂) 2
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  unfold chosenSecondPartialFChartDeriv
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_memLp_of_mem
    h_memW1p l₂

omit [NeZero (Module.finrank ℝ E)] in
private lemma chosenSecondPartialWeakPartialDeriv_memLp
    {g : SmoothRiemannianMetric I M} {α : M}
    {D₁ : DiffChartBilinearH1ComplData (I := I) (M := M) g α}
    {i : Fin (Module.finrank ℝ E)}
    (h_memW1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (D₁.weak_partial_deriv i) (chartTargetEuclid (I := I) (M := M) α))
    (l₂ : Fin (Module.finrank ℝ E)) :
    MemLp (chosenSecondPartialWeakPartialDeriv (I := I) (M := M) D₁ i l₂) 2
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  unfold chosenSecondPartialWeakPartialDeriv
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_memLp_of_mem
    h_memW1p l₂

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma memLp_restrict_of_memLp_chartTarget
    (α : M)
    {f : EuclN → ℝ}
    (hf : MemLp f 2 ((volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α)))
    {K : Set EuclN} (hK_compact : IsCompact K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    MemLp f 2 ((volume : Measure EuclN).restrict K) := by
  have hK_meas : MeasurableSet K := hK_compact.isClosed.measurableSet
  have h_eq : ((volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α)).restrict K =
        (volume : Measure EuclN).restrict K := by
    rw [Measure.restrict_restrict hK_meas]
    congr 1
    exact Set.inter_eq_self_of_subset_left hK_in
  rw [← h_eq]
  exact hf.restrict K

noncomputable def diffTwiceChartBilinearH1ComplData_of_diff
    {g : SmoothRiemannianMetric I M} {α : M}
    (D₁ : DiffChartBilinearH1ComplData (I := I) (M := M) g α)
    (l₂ : Fin (Module.finrank ℝ E))
    (h_uDeriv_memW1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      D₁.u_chart_deriv (chartTargetEuclid (I := I) (M := M) α))
    (h_fDeriv_memW1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      D₁.f_chart_deriv (chartTargetEuclid (I := I) (M := M) α))
    (h_wpDeriv_memW1p : ∀ i, DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (D₁.weak_partial_deriv i) (chartTargetEuclid (I := I) (M := M) α))
    (h_identity :
      ∀ ψ : EuclN → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α →
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i j y *
                (chosenSecondPartialWeakPartialDeriv (I := I) (M := M) D₁ i l₂) y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(volume : Measure EuclN)) +
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            (chosenSecondPartialUChartDeriv (I := I) (M := M) D₁ l₂) y * ψ y
          ∂(volume : Measure EuclN)) =
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            (chosenSecondPartialFChartDeriv (I := I) (M := M) D₁ l₂) y * ψ y
          ∂(volume : Measure EuclN)) -
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramDerivOnEuclid (I := I) g α i j l₂ y *
                (chosenSecondPartialWeakPartialDeriv (I := I) (M := M) D₁ i l₂) y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(volume : Measure EuclN)) -
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityDerivOnEuclid (I := I) g α l₂ y *
            (chosenSecondPartialUChartDeriv (I := I) (M := M) D₁ l₂) y * ψ y
          ∂(volume : Measure EuclN)) +
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityDerivOnEuclid (I := I) g α l₂ y *
            (chosenSecondPartialFChartDeriv (I := I) (M := M) D₁ l₂) y * ψ y
          ∂(volume : Measure EuclN)) -
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramDerivOnEuclid (I := I) g α i j D₁.direction y *
                (chosenSecondPartialWeakPartialDeriv (I := I) (M := M) D₁ i l₂) y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(volume : Measure EuclN)) -
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramSecondDerivOnEuclid (I := I) g α i j
                  D₁.direction l₂ y *
                D₁.base.weak_partial i y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(volume : Measure EuclN)) -
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densitySecondDerivOnEuclid (I := I) g α
              D₁.direction l₂ y *
            D₁.base.u_chart y * ψ y
          ∂(volume : Measure EuclN)) -
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityDerivOnEuclid (I := I) g α D₁.direction y *
            D₁.base.weak_partial l₂ y * ψ y
          ∂(volume : Measure EuclN)) +
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densitySecondDerivOnEuclid (I := I) g α
              D₁.direction l₂ y *
            D₁.base.f_chart y * ψ y
          ∂(volume : Measure EuclN)) +
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityDerivOnEuclid (I := I) g α D₁.direction y *
            (chosenSecondPartialFChartDeriv (I := I) (M := M) D₁ l₂) y * ψ y
          ∂(volume : Measure EuclN))) :
    DiffTwiceChartBilinearH1ComplData (I := I) (M := M) g α where
  base1 := D₁
  direction2 := l₂
  u_chart_deriv2 := chosenSecondPartialUChartDeriv (I := I) (M := M) D₁ l₂
  f_chart_deriv2 := chosenSecondPartialFChartDeriv (I := I) (M := M) D₁ l₂
  u_chart_second_deriv := chosenSecondPartialUChartDeriv (I := I) (M := M) D₁ l₂
  weak_partial_deriv2 := fun i =>
    chosenSecondPartialWeakPartialDeriv (I := I) (M := M) D₁ i l₂
  weak_partial_second_deriv := fun i =>
    chosenSecondPartialWeakPartialDeriv (I := I) (M := M) D₁ i l₂
  u_chart_deriv2_isWeakPartial :=
    chosenSecondPartialUChartDeriv_isWeakPartial
      (I := I) (M := M) h_uDeriv_memW1p l₂
  f_chart_deriv2_isWeakPartial :=
    chosenSecondPartialFChartDeriv_isWeakPartial
      (I := I) (M := M) h_fDeriv_memW1p l₂
  u_chart_second_deriv_isWeakPartial :=
    chosenSecondPartialUChartDeriv_isWeakPartial
      (I := I) (M := M) h_uDeriv_memW1p l₂
  weak_partial_deriv2_isWeakPartial := fun i =>
    chosenSecondPartialWeakPartialDeriv_isWeakPartial
      (I := I) (M := M) (h_wpDeriv_memW1p i) l₂
  weak_partial_second_deriv_isWeakPartial := fun i =>
    chosenSecondPartialWeakPartialDeriv_isWeakPartial
      (I := I) (M := M) (h_wpDeriv_memW1p i) l₂
  u_chart_deriv2_locally_memLp := fun _K hK hKin =>
    memLp_restrict_of_memLp_chartTarget (I := I) (M := M) α
      (chosenSecondPartialUChartDeriv_memLp
        (I := I) (M := M) h_uDeriv_memW1p l₂) hK hKin
  f_chart_deriv2_locally_memLp := fun _K hK hKin =>
    memLp_restrict_of_memLp_chartTarget (I := I) (M := M) α
      (chosenSecondPartialFChartDeriv_memLp
        (I := I) (M := M) h_fDeriv_memW1p l₂) hK hKin
  u_chart_second_deriv_locally_memLp := fun _K hK hKin =>
    memLp_restrict_of_memLp_chartTarget (I := I) (M := M) α
      (chosenSecondPartialUChartDeriv_memLp
        (I := I) (M := M) h_uDeriv_memW1p l₂) hK hKin
  weak_partial_deriv2_locally_memLp := fun i _K hK hKin =>
    memLp_restrict_of_memLp_chartTarget (I := I) (M := M) α
      (chosenSecondPartialWeakPartialDeriv_memLp
        (I := I) (M := M) (h_wpDeriv_memW1p i) l₂) hK hKin
  weak_partial_second_deriv_locally_memLp := fun i _K hK hKin =>
    memLp_restrict_of_memLp_chartTarget (I := I) (M := M) α
      (chosenSecondPartialWeakPartialDeriv_memLp
        (I := I) (M := M) (h_wpDeriv_memW1p i) l₂) hK hKin
  twice_differentiated_variational_identity := h_identity

noncomputable def diffTwiceChartBilinearH1ComplData_of_laplacianDomainPow_two
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (l₁ l₂ : Fin (Module.finrank ℝ E))
    (h_base_f_chart_memW1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
        (laplacianDomainPow_succ_subset_laplacianDomain
          (I := I) (M := M) g 1 hu_h)).f_chart
      (chartTargetEuclid (I := I) (M := M) α))
    (h_once_identity :
      ∀ ψ : EuclN → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α →
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i j y *
                (chosenSecondPartialChartPushedU
                  (I := I) (M := M) g α u_h i l₁) y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(volume : Measure EuclN)) +
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
              (laplacianDomainPow_succ_subset_laplacianDomain
                (I := I) (M := M) g 1 hu_h)).weak_partial l₁ y * ψ y
          ∂(volume : Measure EuclN)) =
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            chosenFChartDeriv (I := I) (M := M) g α hu_h l₁ y * ψ y
          ∂(volume : Measure EuclN)) -
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramDerivOnEuclid (I := I) g α i j l₁ y *
                (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
                  (laplacianDomainPow_succ_subset_laplacianDomain
                    (I := I) (M := M) g 1 hu_h)).weak_partial i y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(volume : Measure EuclN)) -
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityDerivOnEuclid (I := I) g α l₁ y *
            (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
              (laplacianDomainPow_succ_subset_laplacianDomain
                (I := I) (M := M) g 1 hu_h)).u_chart y * ψ y
          ∂(volume : Measure EuclN)) +
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityDerivOnEuclid (I := I) g α l₁ y *
            (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
              (laplacianDomainPow_succ_subset_laplacianDomain
                (I := I) (M := M) g 1 hu_h)).f_chart y * ψ y
          ∂(volume : Measure EuclN)))
    (h_uDeriv_memW1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (diffChartBilinearH1ComplData_of_laplacianDomainPow_two
        (I := I) (M := M) g α hu_h l₁
        h_base_f_chart_memW1p h_once_identity).u_chart_deriv
      (chartTargetEuclid (I := I) (M := M) α))
    (h_fDeriv_memW1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (diffChartBilinearH1ComplData_of_laplacianDomainPow_two
        (I := I) (M := M) g α hu_h l₁
        h_base_f_chart_memW1p h_once_identity).f_chart_deriv
      (chartTargetEuclid (I := I) (M := M) α))
    (h_wpDeriv_memW1p : ∀ i,
      DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
        ((diffChartBilinearH1ComplData_of_laplacianDomainPow_two
          (I := I) (M := M) g α hu_h l₁
          h_base_f_chart_memW1p h_once_identity).weak_partial_deriv i)
        (chartTargetEuclid (I := I) (M := M) α))
    (h_twice_identity :
      ∀ ψ : EuclN → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α →
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i j y *
                (chosenSecondPartialWeakPartialDeriv (I := I) (M := M)
                  (diffChartBilinearH1ComplData_of_laplacianDomainPow_two
                    (I := I) (M := M) g α hu_h l₁
                    h_base_f_chart_memW1p h_once_identity) i l₂) y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(volume : Measure EuclN)) +
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            (chosenSecondPartialUChartDeriv (I := I) (M := M)
              (diffChartBilinearH1ComplData_of_laplacianDomainPow_two
                (I := I) (M := M) g α hu_h l₁
                h_base_f_chart_memW1p h_once_identity) l₂) y * ψ y
          ∂(volume : Measure EuclN)) =
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            (chosenSecondPartialFChartDeriv (I := I) (M := M)
              (diffChartBilinearH1ComplData_of_laplacianDomainPow_two
                (I := I) (M := M) g α hu_h l₁
                h_base_f_chart_memW1p h_once_identity) l₂) y * ψ y
          ∂(volume : Measure EuclN)) -
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramDerivOnEuclid (I := I) g α i j l₂ y *
                (chosenSecondPartialWeakPartialDeriv (I := I) (M := M)
                  (diffChartBilinearH1ComplData_of_laplacianDomainPow_two
                    (I := I) (M := M) g α hu_h l₁
                    h_base_f_chart_memW1p h_once_identity) i l₂) y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(volume : Measure EuclN)) -
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityDerivOnEuclid (I := I) g α l₂ y *
            (chosenSecondPartialUChartDeriv (I := I) (M := M)
              (diffChartBilinearH1ComplData_of_laplacianDomainPow_two
                (I := I) (M := M) g α hu_h l₁
                h_base_f_chart_memW1p h_once_identity) l₂) y * ψ y
          ∂(volume : Measure EuclN)) +
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityDerivOnEuclid (I := I) g α l₂ y *
            (chosenSecondPartialFChartDeriv (I := I) (M := M)
              (diffChartBilinearH1ComplData_of_laplacianDomainPow_two
                (I := I) (M := M) g α hu_h l₁
                h_base_f_chart_memW1p h_once_identity) l₂) y * ψ y
          ∂(volume : Measure EuclN)) -
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramDerivOnEuclid (I := I) g α i j
                  (diffChartBilinearH1ComplData_of_laplacianDomainPow_two
                    (I := I) (M := M) g α hu_h l₁
                    h_base_f_chart_memW1p h_once_identity).direction y *
                (chosenSecondPartialWeakPartialDeriv (I := I) (M := M)
                  (diffChartBilinearH1ComplData_of_laplacianDomainPow_two
                    (I := I) (M := M) g α hu_h l₁
                    h_base_f_chart_memW1p h_once_identity) i l₂) y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(volume : Measure EuclN)) -
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramSecondDerivOnEuclid (I := I) g α i j
                  (diffChartBilinearH1ComplData_of_laplacianDomainPow_two
                    (I := I) (M := M) g α hu_h l₁
                    h_base_f_chart_memW1p h_once_identity).direction l₂ y *
                (diffChartBilinearH1ComplData_of_laplacianDomainPow_two
                  (I := I) (M := M) g α hu_h l₁
                  h_base_f_chart_memW1p h_once_identity).base.weak_partial i y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(volume : Measure EuclN)) -
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densitySecondDerivOnEuclid (I := I) g α
              (diffChartBilinearH1ComplData_of_laplacianDomainPow_two
                (I := I) (M := M) g α hu_h l₁
                h_base_f_chart_memW1p h_once_identity).direction l₂ y *
            (diffChartBilinearH1ComplData_of_laplacianDomainPow_two
              (I := I) (M := M) g α hu_h l₁
              h_base_f_chart_memW1p h_once_identity).base.u_chart y * ψ y
          ∂(volume : Measure EuclN)) -
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityDerivOnEuclid (I := I) g α
              (diffChartBilinearH1ComplData_of_laplacianDomainPow_two
                (I := I) (M := M) g α hu_h l₁
                h_base_f_chart_memW1p h_once_identity).direction y *
            (diffChartBilinearH1ComplData_of_laplacianDomainPow_two
              (I := I) (M := M) g α hu_h l₁
              h_base_f_chart_memW1p h_once_identity).base.weak_partial l₂ y *
            ψ y
          ∂(volume : Measure EuclN)) +
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densitySecondDerivOnEuclid (I := I) g α
              (diffChartBilinearH1ComplData_of_laplacianDomainPow_two
                (I := I) (M := M) g α hu_h l₁
                h_base_f_chart_memW1p h_once_identity).direction l₂ y *
            (diffChartBilinearH1ComplData_of_laplacianDomainPow_two
              (I := I) (M := M) g α hu_h l₁
              h_base_f_chart_memW1p h_once_identity).base.f_chart y * ψ y
          ∂(volume : Measure EuclN)) +
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityDerivOnEuclid (I := I) g α
              (diffChartBilinearH1ComplData_of_laplacianDomainPow_two
                (I := I) (M := M) g α hu_h l₁
                h_base_f_chart_memW1p h_once_identity).direction y *
            (chosenSecondPartialFChartDeriv (I := I) (M := M)
              (diffChartBilinearH1ComplData_of_laplacianDomainPow_two
                (I := I) (M := M) g α hu_h l₁
                h_base_f_chart_memW1p h_once_identity) l₂) y * ψ y
          ∂(volume : Measure EuclN))) :
    DiffTwiceChartBilinearH1ComplData (I := I) (M := M) g α :=
  diffTwiceChartBilinearH1ComplData_of_diff (I := I) (M := M)
    (diffChartBilinearH1ComplData_of_laplacianDomainPow_two
      (I := I) (M := M) g α hu_h l₁
      h_base_f_chart_memW1p h_once_identity)
    l₂
    h_uDeriv_memW1p h_fDeriv_memW1p h_wpDeriv_memW1p
    h_twice_identity

end DiffTwiceChartBilinearH1Compl
end Laplacian
end Analysis
end DifferentialGeometry

end
