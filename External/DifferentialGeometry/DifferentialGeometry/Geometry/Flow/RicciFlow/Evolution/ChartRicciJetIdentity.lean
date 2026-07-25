import DifferentialGeometry.Geometry.Curvature.Riemann.Defs
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.ChristoffelPerturbation
import DifferentialGeometry.Geometry.Operator.HessianTrace
import DifferentialGeometry.Geometry.Connection.ChartBridge.RiemannBasisIdentityOffCentre
import DifferentialGeometry.Analysis.Calculus.SmoothExtension.JetPartialDeriv
import DifferentialGeometry.Analysis.Calculus.SmoothExtension.JetGlueParam
import DifferentialGeometry.Analysis.Calculus.TimeJetEvolution



















noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold Topology ContDiff Matrix
open DifferentialGeometry.Analysis DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients
open DifferentialGeometry.Integral.Connection

namespace DifferentialGeometry
namespace Integral
namespace DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]



def chartGramPi (g : SmoothRiemannianMetric I M) (α : M) :
    E → (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) :=
  fun w l m => chartGramOnE (I := I) g α l m w

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
@[simp] theorem chartGramPi_apply (g : SmoothRiemannianMetric I M) (α : M) (w : E)
    (l m : Fin (Module.finrank ℝ E)) :
    chartGramPi (I := I) g α w l m = chartGramOnE (I := I) g α l m w := rfl


omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem jet2_chartGram_d1 (g : SmoothRiemannianMetric I M) (α : M) {y : E}
    (hG : DifferentiableAt ℝ (chartGramPi (I := I) g α) y)
    (i l m : Fin (Module.finrank ℝ E)) :
    (jet2 (chartGramPi (I := I) g α) y).2.1 (chartModelBasis E i) l m
      = partialDeriv (E := E) i (chartGramOnE (I := I) g α l m) y := by
  simp only [jet2]
  rw [fderiv_matEntry hG (chartModelBasis E i) l m]
  rfl



omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem jet2_chartGram_d2 (g : SmoothRiemannianMetric I M) (α : M) {y : E}
    (hG1 : ∀ w, DifferentiableAt ℝ (chartGramPi (I := I) g α) w)
    (hG2 : DifferentiableAt ℝ (fun w => fderiv ℝ (chartGramPi (I := I) g α) w) y)
    (m i l j : Fin (Module.finrank ℝ E)) :
    (jet2 (chartGramPi (I := I) g α) y).2.2 (chartModelBasis E m) (chartModelBasis E i) l j
      = partialDeriv (E := E) m (partialDeriv (E := E) i (chartGramOnE (I := I) g α l j)) y := by
  simp only [jet2]
  rw [fderiv2_matEntry hG2 (chartModelBasis E m) (chartModelBasis E i) l j]
  have hinner : (fun w => (fderiv ℝ (chartGramPi (I := I) g α) w) (chartModelBasis E i) l j)
      = partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) := by
    funext w
    rw [fderiv_matEntry (hG1 w) (chartModelBasis E i) l j]
    rfl
  rw [hinner]
  rfl



omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem jet2_chartGram_invGram (g : SmoothRiemannianMetric I M) (α : M) (y : E)
    (k l : Fin (Module.finrank ℝ E)) :
    (Matrix.of (jet2 (chartGramPi (I := I) g α) y).1)⁻¹ k l = chartInvGramOnE (I := I) g α k l y := by
  have hmat : Matrix.of (jet2 (chartGramPi (I := I) g α) y).1
      = chartGramMatrix (I := I) g α ((extChartAt I α).symm y) := by
    ext a b
    simp only [jet2, chartGramPi, chartGramOnE_def, Matrix.of_apply]
  rw [hmat, chartInvGramOnE_def]
  simp only [chartInvGramMatrix]



omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem chartChristoffel_eq_jet (g : SmoothRiemannianMetric I M) (α : M) {y : E}
    (hG : DifferentiableAt ℝ (chartGramPi (I := I) g α) y) (i j k : Fin (Module.finrank ℝ E)) :
    chartChristoffel (I := I) g α i j k y
      = jetChristoffel (chartModelBasis E) (jet2 (chartGramPi (I := I) g α) y) i j k := by
  rw [chartChristoffel_def]
  simp only [jetChristoffel]
  congr 1
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [jet2_chartGram_invGram g α y k l, chartInvGramOnE_def,
    jet2_chartGram_d1 g α hG i l j, jet2_chartGram_d1 g α hG j l i, jet2_chartGram_d1 g α hG l i j]




omit [InnerProductSpace ℝ E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem chartChristoffelDeriv_eq_jet (g : SmoothRiemannianMetric I M) (α : M) {y : E}
    (hy : y ∈ interior (extChartAt I α).target)
    (hG : DifferentiableAt ℝ (chartGramPi (I := I) g α) y)
    (hG1 : ∀ w, DifferentiableAt ℝ (chartGramPi (I := I) g α) w)
    (hG2 : DifferentiableAt ℝ (fun w => fderiv ℝ (chartGramPi (I := I) g α) w) y)
    (m i j k : Fin (Module.finrank ℝ E)) :
    partialDeriv (E := E) m (chartChristoffel (I := I) g α i j k) y
      = jetChristoffelDeriv (chartModelBasis E) (jet2 (chartGramPi (I := I) g α) y) m i j k := by
  rw [partialDeriv_chartChristoffel_eq g α m i j k hy]
  simp only [jetChristoffelDeriv]
  congr 1
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [partialDeriv_chartInvGramOnE_eq g α y m k l hy]
  simp only [gramBracket, gramBracketDeriv, jet2_chartGram_invGram g α y,
    jet2_chartGram_d1 g α hG, jet2_chartGram_d2 g α hG1 hG2]



omit [InnerProductSpace ℝ E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem chartRiemann_eq_jet (g : SmoothRiemannianMetric I M) (α : M) {y : E}
    (hy : y ∈ interior (extChartAt I α).target)
    (hG : DifferentiableAt ℝ (chartGramPi (I := I) g α) y)
    (hG1 : ∀ w, DifferentiableAt ℝ (chartGramPi (I := I) g α) w)
    (hG2 : DifferentiableAt ℝ (fun w => fderiv ℝ (chartGramPi (I := I) g α) w) y)
    (i j k l : Fin (Module.finrank ℝ E)) :
    chartRiemannTensor (I := I) g α i j k l y
      = jetRiemann (chartModelBasis E) (jet2 (chartGramPi (I := I) g α) y) i j k l := by
  rw [chartRiemannTensor_def]
  simp only [jetRiemann]
  rw [chartChristoffelDeriv_eq_jet g α hy hG hG1 hG2 j i k l,
    chartChristoffelDeriv_eq_jet g α hy hG hG1 hG2 k i j l]
  congr 1
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [chartChristoffel_eq_jet g α hG j m l, chartChristoffel_eq_jet g α hG i k m,
    chartChristoffel_eq_jet g α hG k m l, chartChristoffel_eq_jet g α hG i j m]



omit [InnerProductSpace ℝ E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem chartRicci_eq_jet (g : SmoothRiemannianMetric I M) (α : M) {y : E}
    (hy : y ∈ interior (extChartAt I α).target)
    (hG : DifferentiableAt ℝ (chartGramPi (I := I) g α) y)
    (hG1 : ∀ w, DifferentiableAt ℝ (chartGramPi (I := I) g α) w)
    (hG2 : DifferentiableAt ℝ (fun w => fderiv ℝ (chartGramPi (I := I) g α) w) y)
    (i k : Fin (Module.finrank ℝ E)) :
    chartRicciTensor (I := I) g α i k y
      = jetRicci (chartModelBasis E) (jet2 (chartGramPi (I := I) g α) y) i k := by
  rw [chartRicciTensor_def]
  simp only [jetRicci]
  exact Finset.sum_congr rfl (fun j _ => chartRiemann_eq_jet g α hy hG hG1 hG2 i j k j)




omit [InnerProductSpace ℝ E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem jetRicciFlow_chartGram (g : SmoothRiemannianMetric I M) (α : M) {y : E}
    (hy : y ∈ interior (extChartAt I α).target)
    (hG : DifferentiableAt ℝ (chartGramPi (I := I) g α) y)
    (hG1 : ∀ w, DifferentiableAt ℝ (chartGramPi (I := I) g α) w)
    (hG2 : DifferentiableAt ℝ (fun w => fderiv ℝ (chartGramPi (I := I) g α) w) y)
    (i k : Fin (Module.finrank ℝ E)) :
    jetRicciFlow (chartModelBasis E) (jet2 (chartGramPi (I := I) g α) y) i k
      = -2 * chartRicciTensor (I := I) g α i k y := by
  rw [jetRicciFlow, chartRicci_eq_jet g α hy hG hG1 hG2 i k]







omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem ricciFlowChartGram_jetMatch (g₁ g₂ : ℝ → SmoothRiemannianMetric I M) (α : M)
    {V : Set E} {sL sR : Set ℝ}
    (hsL : UniqueDiffOn ℝ sL) (haccL : sL ⊆ closure (interior sL)) (h0L : (0 : ℝ) ∈ sL)
    (hsR : UniqueDiffOn ℝ sR) (haccR : sR ⊆ closure (interior sR)) (h0R : (0 : ℝ) ∈ sR)
    (hV : IsOpen V)
    (hGL : ContDiffOn ℝ ∞ (Function.uncurry (fun t => chartGramPi (I := I) (g₁ t) α)) (sL ×ˢ V))
    (hGR : ContDiffOn ℝ ∞ (Function.uncurry (fun t => chartGramPi (I := I) (g₂ t) α)) (sR ×ˢ V))
    (hcurveL : ∀ w ∈ V,
      ContDiffWithinAt ℝ ∞ (fun t => jet2 (chartGramPi (I := I) (g₁ t) α) w) sL 0)
    (hcurveR : ∀ w ∈ V,
      ContDiffWithinAt ℝ ∞ (fun t => jet2 (chartGramPi (I := I) (g₂ t) α) w) sR 0)
    (hdet : ∀ w ∈ V, (Matrix.of (jet2 (chartGramPi (I := I) (g₁ 0) α) w).1).det ≠ 0)
    (hevolL : ∀ t ∈ sL, ∀ w ∈ V, derivWithin (fun s => chartGramPi (I := I) (g₁ s) α w) sL t
      = jetRicciFlow (chartModelBasis E) (jet2 (chartGramPi (I := I) (g₁ t) α) w))
    (hevolR : ∀ t ∈ sR, ∀ w ∈ V, derivWithin (fun s => chartGramPi (I := I) (g₂ s) α w) sR t
      = jetRicciFlow (chartModelBasis E) (jet2 (chartGramPi (I := I) (g₂ t) α) w))
    (hbdry : Set.EqOn (chartGramPi (I := I) (g₁ 0) α) (chartGramPi (I := I) (g₂ 0) α) V) :
    ∀ (n : ℕ), ∀ w ∈ V,
      iteratedDerivWithin n (fun s => chartGramPi (I := I) (g₁ s) α w) sL 0
        = iteratedDerivWithin n (fun s => chartGramPi (I := I) (g₂ s) α w) sR 0 :=
  jetMatch_of_evolution hsL haccL h0L hsR haccR h0R hV hGL hGR
    (fun w hw => contDiffAt_jetRicciFlow (chartModelBasis E) (hdet w hw))
    hcurveL hcurveR hevolL hevolR hbdry







omit [InnerProductSpace ℝ E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem chartGramEvolution_of_pde (g : ℝ → SmoothRiemannianMetric I M) (α : M) {y : E} {sL : Set ℝ}
    {t : ℝ} (hsL : UniqueDiffWithinAt ℝ sL t)
    (hy : y ∈ interior (extChartAt I α).target)
    (hG : DifferentiableAt ℝ (chartGramPi (I := I) (g t) α) y)
    (hG1 : ∀ w, DifferentiableAt ℝ (chartGramPi (I := I) (g t) α) w)
    (hG2 : DifferentiableAt ℝ (fun w => fderiv ℝ (chartGramPi (I := I) (g t) α) w) y)
    (hpde : ∀ i k : Fin (Module.finrank ℝ E),
      HasDerivWithinAt (fun s => chartGramOnE (I := I) (g s) α i k y)
        (-2 * chartRicciTensor (I := I) (g t) α i k y) sL t) :
    derivWithin (fun s => chartGramPi (I := I) (g s) α y) sL t
      = jetRicciFlow (chartModelBasis E) (jet2 (chartGramPi (I := I) (g t) α) y) := by
  have hderiv : HasDerivWithinAt (fun s => chartGramPi (I := I) (g s) α y)
      (fun i k => -2 * chartRicciTensor (I := I) (g t) α i k y) sL t := by
    rw [hasDerivWithinAt_pi]
    intro i
    rw [hasDerivWithinAt_pi]
    intro k
    exact hpde i k
  rw [hderiv.derivWithin hsL]
  funext i k
  exact (jetRicciFlow_chartGram (g t) α hy hG hG1 hG2 i k).symm








omit [InnerProductSpace ℝ E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem chartGramEntryPDE_of_metricPDE [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]
    (g : ℝ → SmoothRiemannianMetric I M) (α : M) {y : E} {sL : Set ℝ} {t : ℝ}
    (hgs : (extChartAt I α).symm y ∈ chartLeviCivitaGoodSet (I := I) α)
    (hyt : extChartAt I α ((extChartAt I α).symm y) = y) (i k : Fin (Module.finrank ℝ E))
    (hmpde : HasDerivWithinAt
      (fun s => (g s).inner ((extChartAt I α).symm y)
        (chartBasisVecFiber (I := I) α i ((extChartAt I α).symm y))
        (chartBasisVecFiber (I := I) α k ((extChartAt I α).symm y)))
      (-2 * ricciTensor (I := I) (g t) ((extChartAt I α).symm y)
        (chartBasisVecFiber (I := I) α i ((extChartAt I α).symm y))
        (chartBasisVecFiber (I := I) α k ((extChartAt I α).symm y))) sL t) :
    HasDerivWithinAt (fun s => chartGramOnE (I := I) (g s) α i k y)
      (-2 * chartRicciTensor (I := I) (g t) α i k y) sL t := by
  have hbridge : ricciTensor (I := I) (g t) ((extChartAt I α).symm y)
        (chartBasisVecFiber (I := I) α i ((extChartAt I α).symm y))
        (chartBasisVecFiber (I := I) α k ((extChartAt I α).symm y))
      = chartRicciTensor (I := I) (g t) α i k y := by
    rw [ricciTensor_chartBasisVec_alpha_eq (g t) α i k hgs, hyt]
  rw [← hbridge]
  exact hmpde








omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem chartGramGlue_contDiffOn (g₁ g₂ : ℝ → SmoothRiemannianMetric I M) (α : M) {V : Set E}
    (hV : IsOpen V)
    (hL : ContDiffOn ℝ ∞ (Function.uncurry (fun t => chartGramPi (I := I) (g₁ t) α))
      (Set.Iic 0 ×ˢ V))
    (hR : ContDiffOn ℝ ∞ (Function.uncurry (fun t => chartGramPi (I := I) (g₂ t) α))
      (Set.Ici 0 ×ˢ V))
    (hcurveL : ∀ w ∈ V,
      ContDiffWithinAt ℝ ∞ (fun t => jet2 (chartGramPi (I := I) (g₁ t) α) w) (Set.Iic 0) 0)
    (hcurveR : ∀ w ∈ V,
      ContDiffWithinAt ℝ ∞ (fun t => jet2 (chartGramPi (I := I) (g₂ t) α) w) (Set.Ici 0) 0)
    (hdet : ∀ w ∈ V, (Matrix.of (jet2 (chartGramPi (I := I) (g₁ 0) α) w).1).det ≠ 0)
    (hevolL : ∀ t ∈ Set.Iic (0 : ℝ), ∀ w ∈ V,
      derivWithin (fun s => chartGramPi (I := I) (g₁ s) α w) (Set.Iic 0) t
        = jetRicciFlow (chartModelBasis E) (jet2 (chartGramPi (I := I) (g₁ t) α) w))
    (hevolR : ∀ t ∈ Set.Ici (0 : ℝ), ∀ w ∈ V,
      derivWithin (fun s => chartGramPi (I := I) (g₂ s) α w) (Set.Ici 0) t
        = jetRicciFlow (chartModelBasis E) (jet2 (chartGramPi (I := I) (g₂ t) α) w))
    (hbdry : Set.EqOn (chartGramPi (I := I) (g₁ 0) α) (chartGramPi (I := I) (g₂ 0) α) V) :
    ContDiffOn ℝ ∞
      (fun q : ℝ × E => if q.1 ≤ 0 then Function.uncurry (fun t => chartGramPi (I := I) (g₁ t) α) q
        else Function.uncurry (fun t => chartGramPi (I := I) (g₂ t) α) q)
      (Set.univ ×ˢ V) := by
  have heqL : closure (interior (Set.Iic (0 : ℝ))) = Set.Iic 0 := by rw [interior_Iic, closure_Iio]
  have heqR : closure (interior (Set.Ici (0 : ℝ))) = Set.Ici 0 := by rw [interior_Ici, closure_Ioi]
  refine SmoothExtension.contDiffOn_glue_of_jet_param hV _ _ hL hR (fun i w hw => ?_)
  exact ricciFlowChartGram_jetMatch g₁ g₂ α (uniqueDiffOn_Iic 0) heqL.ge (Set.mem_Iic.mpr le_rfl)
    (uniqueDiffOn_Ici 0) heqR.ge (Set.mem_Ici.mpr le_rfl) hV hL hR hcurveL hcurveR hdet
    hevolL hevolR hbdry i w hw

end DivergenceTheorem
end Integral
end DifferentialGeometry

end
