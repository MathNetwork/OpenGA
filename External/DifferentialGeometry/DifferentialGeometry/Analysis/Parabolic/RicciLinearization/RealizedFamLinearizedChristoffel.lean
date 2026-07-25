import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RealizedFamChartRicciDeriv
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.ChristoffelLinearization


noncomputable section

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace PDE
namespace DeTurck
namespace RicciLinearization

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

def realizedLinearizedChristoffelPrincipal (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (i j k : Fin (Module.finrank ℝ E)) (y : E) (s₀ : ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
    chartInvGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀) x k l y *
      (partialDeriv (E := E) i
          (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x l j) y +
        partialDeriv (E := E) j
          (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x l i) y -
        partialDeriv (E := E) l
          (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i j) y)

def realizedChristoffelNonPrincipal (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (i j k : Fin (Module.finrank ℝ E)) (y : E) (s₀ : ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
    (-(∑ q : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀) x k p y *
          realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x p q y *
          chartInvGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀) x q l y)) *
      gramBracket (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀) x i j l y

omit [BoundarylessManifold I M] in
omit [CompactSpace M] in
theorem linearizedChristoffel_eq_principal_add_nonPrincipal
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (i j k : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I x).target) {s₀ : ℝ}
    (hs₀ : s₀ ∈ realizedSmallSet (δ := δ) (δ' := δ')) :
    deriv (fun s : ℝ =>
        chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x i j k y) s₀ =
      realizedLinearizedChristoffelPrincipal (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i j k y s₀ +
        realizedChristoffelNonPrincipal (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i j k y s₀ := by
  classical
  rw [(hasDerivAt_realizedFam_chartChristoffel
    (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i j k hy hs₀).deriv]
  rw [realizedLinearizedChristoffelPrincipal, realizedChristoffelNonPrincipal]
  rw [← mul_add, ← Finset.sum_add_distrib]
  refine congrArg (HMul.hMul (1 / 2 : ℝ)) (Finset.sum_congr rfl (fun l _ => ?_))
  ring

omit [BoundarylessManifold I M] in
omit [CompactSpace M] in
theorem realizedLinearizedChristoffelPrincipal_eq_chartLinearizedPrincipal
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (i j k : Fin (Module.finrank ℝ E)) (y : E) (s₀ : ℝ)
    (h : ChartMetricPerturbation E)
    (hh : ∀ a b : Fin (Module.finrank ℝ E),
      Set.EqOn (h a b) (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x a b)
        (extChartAt I x).target)
    (hy : y ∈ (extChartAt I x).target) :
    realizedLinearizedChristoffelPrincipal (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i j k y s₀ =
      chartLinearizedChristoffelPrincipal (I := I)
        (realizedFam (I := I) g₀ T T' hδ hδ' s₀) x h i j k y := by
  classical
  rw [realizedLinearizedChristoffelPrincipal, chartLinearizedChristoffelPrincipal_def]
  refine congrArg (HMul.hMul (1 / 2 : ℝ)) (Finset.sum_congr rfl (fun l _ => ?_))
  have hopen : IsOpen (extChartAt I x).target := isOpen_extChartAt_target x
  have hpd : ∀ a b c : Fin (Module.finrank ℝ E),
      partialDeriv (E := E) a (h b c) y =
        partialDeriv (E := E) a (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x b c) y := by
    intro a b c
    have hEv : (h b c) =ᶠ[nhds y]
        (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x b c) :=
      Filter.eventuallyEq_of_mem (hopen.mem_nhds hy) (hh b c)
    unfold partialDeriv
    rw [hEv.fderiv_eq]
  rw [hpd i l j, hpd j l i, hpd l i j]

omit [BoundarylessManifold I M] in
omit [CompactSpace M] in
theorem realizedGramDeriv_self_eq_zero (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (α : M) (i j : Fin (Module.finrank ℝ E)) (y : E) :
    realizedGramDeriv (I := I) g₀ T T hδ_lt hδ hδ_lt hδ α i j y = 0 := by
  rw [realizedGramDeriv, sub_self]

omit [BoundarylessManifold I M] in
omit [CompactSpace M] in
theorem realizedLinearizedChristoffelPrincipal_self_eq_zero
    (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (x : M) (i j k : Fin (Module.finrank ℝ E)) (y : E) (s₀ : ℝ) :
    realizedLinearizedChristoffelPrincipal (I := I) g₀ T T hδ_lt hδ hδ_lt hδ x i j k y s₀ = 0 := by
  classical
  rw [realizedLinearizedChristoffelPrincipal]
  have hzero : ∀ l : Fin (Module.finrank ℝ E),
      chartInvGramOnE (I := I) (realizedFam (I := I) g₀ T T hδ hδ s₀) x k l y *
        (partialDeriv (E := E) i
            (realizedGramDeriv (I := I) g₀ T T hδ_lt hδ hδ_lt hδ x l j) y +
          partialDeriv (E := E) j
            (realizedGramDeriv (I := I) g₀ T T hδ_lt hδ hδ_lt hδ x l i) y -
          partialDeriv (E := E) l
            (realizedGramDeriv (I := I) g₀ T T hδ_lt hδ hδ_lt hδ x i j) y) = 0 := by
    intro l
    have h1 : (realizedGramDeriv (I := I) g₀ T T hδ_lt hδ hδ_lt hδ x l j) = fun _ : E => (0 : ℝ) := by
      funext z; exact realizedGramDeriv_self_eq_zero (I := I) g₀ T hδ_lt hδ x l j z
    have h2 : (realizedGramDeriv (I := I) g₀ T T hδ_lt hδ hδ_lt hδ x l i) = fun _ : E => (0 : ℝ) := by
      funext z; exact realizedGramDeriv_self_eq_zero (I := I) g₀ T hδ_lt hδ x l i z
    have h3 : (realizedGramDeriv (I := I) g₀ T T hδ_lt hδ hδ_lt hδ x i j) = fun _ : E => (0 : ℝ) := by
      funext z; exact realizedGramDeriv_self_eq_zero (I := I) g₀ T hδ_lt hδ x i j z
    rw [h1, h2, h3, partialDeriv_const, partialDeriv_const, partialDeriv_const]
    ring
  rw [Finset.sum_congr rfl (fun l _ => hzero l), Finset.sum_const_zero, mul_zero]

end RicciLinearization
end DeTurck
end PDE
end DifferentialGeometry

end
