import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.LieSummandLipschitz
import DifferentialGeometry.Geometry.Flow.DeTurckVFChartCoord
import DifferentialGeometry.Geometry.Flow.LieDerivativeMetric


noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff Matrix BigOperators

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral
namespace DeTurckCoefficients

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.DeTurck
open DifferentialGeometry.PDE.DeTurck.DeTurckLinearization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] [I.Boundaryless]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] [I.Boundaryless] in
lemma chartCoeff_eq_repr_trivToE (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (k : Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    chartCoeff (I := I) α X k x =
      ((chartModelBasis E).repr (trivToE (I := I) α x (X x))) k := by
  rw [chartCoeff_def]
  congr 1
  rw [trivToE,
    (trivializationAt E (TangentSpace I) α).continuousLinearMapAt_apply ℝ,
    (trivializationAt E (TangentSpace I) α).coe_linearMapAt_of_mem hx]

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem chartCoeff_deTurckVF_eq_chartDeTurckVFComp
    (g g_bg : SmoothRiemannianMetric I M) (α : M)
    (k : Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) :
    chartCoeff (I := I) α (deTurckVF (I := I) g g_bg) k x =
      chartDeTurckVFComp (I := I) g g_bg α k (extChartAt I α x) := by
  classical
  have hx_base : x ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hx
  rw [chartCoeff_eq_repr_trivToE (I := I) α (deTurckVF (I := I) g g_bg) k hx_base]
  rw [deTurckVF_apply_eq_chartDeTurckVFComp_sum (I := I) g g_bg α hx]
  rw [map_sum]
  rw [map_sum]
  simp only [Finsupp.coe_finset_sum, Finset.sum_apply]
  have hbasis : ∀ p : Fin (Module.finrank ℝ E),
      ((chartModelBasis E).repr (trivToE (I := I) α x
          (chartDeTurckVFComp (I := I) g g_bg α p (extChartAt I α x) •
            chartBasisVecFiber (I := I) α p x))) k =
        (if p = k then chartDeTurckVFComp (I := I) g g_bg α p (extChartAt I α x)
          else 0) := by
    intro p
    rw [map_smul]
    have htriv : trivToE (I := I) α x (chartBasisVecFiber (I := I) α p x) =
        (chartModelBasis E) p := by
      have : chartBasisVecFiber (I := I) α p x =
          trivFromE (I := I) α x ((chartModelBasis E) p) := rfl
      rw [this, trivToE_trivFromE (I := I) α hx_base ((chartModelBasis E) p)]
    rw [htriv, map_smul, Finsupp.smul_apply, Module.Basis.repr_self,
      Finsupp.single_apply, smul_eq_mul]
    by_cases hpk : p = k
    · rw [if_pos hpk, if_pos hpk, mul_one]
    · rw [if_neg hpk, if_neg hpk, mul_zero]
  rw [Finset.sum_congr rfl (fun p _ => hbasis p)]
  rw [Finset.sum_ite_eq' Finset.univ k
    (fun p => chartDeTurckVFComp (I := I) g g_bg α p (extChartAt I α x))]
  rw [if_pos (Finset.mem_univ k)]

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem chartCoeffOnE_deTurckVF_eqOn_goodSet_image
    (g g_bg : SmoothRiemannianMetric I M) (α : M)
    (k : Fin (Module.finrank ℝ E)) :
    Set.EqOn (chartCoeffOnE (I := I) α (deTurckVF (I := I) g g_bg) k)
      (chartDeTurckVFComp (I := I) g g_bg α k)
      ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) := by
  rintro y ⟨b, hb_good, rfl⟩
  have hb_src : b ∈ (extChartAt I α).source :=
    chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) hb_good
  rw [chartCoeffOnE, (extChartAt I α).left_inv hb_src]
  exact chartCoeff_deTurckVF_eq_chartDeTurckVFComp (I := I) g g_bg α k hb_good

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem partialDeriv_chartCoeffOnE_deTurckVF_eq
    (g g_bg : SmoothRiemannianMetric I M) (α : M)
    (m k : Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) :
    partialDeriv (E := E) m
        (chartCoeffOnE (I := I) α (deTurckVF (I := I) g g_bg) k) (extChartAt I α x) =
      partialDeriv (E := E) m
        (chartDeTurckVFComp (I := I) g g_bg α k) (extChartAt I α x) := by
  have hU_open : IsOpen ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) :=
    chartLeviCivitaGoodSet_image_isOpen (I := I) α
  have hx_mem : extChartAt I α x ∈
      (extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α := ⟨x, hx, rfl⟩
  have heqOn := chartCoeffOnE_deTurckVF_eqOn_goodSet_image (I := I) g g_bg α k
  have heventually :
      chartCoeffOnE (I := I) α (deTurckVF (I := I) g g_bg) k =ᶠ[𝓝 (extChartAt I α x)]
        chartDeTurckVFComp (I := I) g g_bg α k :=
    heqOn.eventuallyEq_of_mem (hU_open.mem_nhds hx_mem)
  rw [partialDeriv, partialDeriv, heventually.fderiv_eq]

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem chartLieDerivMetricMatrix_deTurckVF_eq_chartLieDeTurckComp
    (g g_bg : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) :
    chartLieDerivMetricMatrix (I := I) g (deTurckVF (I := I) g g_bg) α i j x =
      chartLieDeTurckComp (I := I) g g_bg α i j (extChartAt I α x) := by
  classical
  have hx_src : x ∈ (extChartAt I α).source :=
    chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) hx
  have hgram : ∀ a b : Fin (Module.finrank ℝ E),
      chartGramMatrix (I := I) g α x a b =
        chartGramOnE (I := I) g α a b (extChartAt I α x) := by
    intro a b
    rw [chartGramOnE, (extChartAt I α).left_inv hx_src]
  rw [chartLieDerivMetricMatrix_def, chartLieDeTurckComp_def]
  refine congr_arg₂ (· + ·) (congr_arg₂ (· + ·) ?_ ?_) ?_
  · refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [chartCoeff_deTurckVF_eq_chartDeTurckVFComp (I := I) g g_bg α k hx]
  · refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hgram k j,
      partialDeriv_chartCoeffOnE_deTurckVF_eq (I := I) g g_bg α i k hx]
  · refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hgram i k,
      partialDeriv_chartCoeffOnE_deTurckVF_eq (I := I) g g_bg α j k hx]

end DeTurckCoefficients
end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
