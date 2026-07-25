import DifferentialGeometry.Integration.DivergenceTheorem.Gradient
import DifferentialGeometry.Geometry.Operator.Hessian
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.ChristoffelPerturbation

set_option autoImplicit false
set_option linter.style.longLine false





















namespace DifferentialGeometry.Integral.Connection

open Bundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E] [CompleteSpace E]
variable [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem







private lemma traceChristoffelAlg
    {Idx : Type*} [Fintype Idx]
    (gInv : Idx → Idx → ℝ) (D : Idx → Idx → Idx → ℝ)
    (hsym : ∀ i j : Idx, gInv i j = gInv j i) (p : Idx) :
    (∑ a : Idx,
        (1 / 2 : ℝ) *
          ∑ l : Idx, gInv a l * (D p a l + D a p l - D l p a))
      =
    (1 / 2 : ℝ) * ∑ i : Idx, ∑ j : Idx, gInv i j * D p i j := by
  classical
  let S₁ : ℝ := ∑ a : Idx, ∑ l : Idx, gInv a l * D p a l
  let S₂ : ℝ := ∑ a : Idx, ∑ l : Idx, gInv a l * D a p l
  let S₃ : ℝ := ∑ a : Idx, ∑ l : Idx, gInv a l * D l p a
  have hS₃ : S₃ = S₂ := by
    unfold S₂ S₃
    calc
      (∑ a : Idx, ∑ l : Idx, gInv a l * D l p a)
          = ∑ l : Idx, ∑ a : Idx, gInv a l * D l p a := by
            rw [Finset.sum_comm]
      _ = ∑ l : Idx, ∑ a : Idx, gInv l a * D l p a := by
            refine Finset.sum_congr rfl fun l _ => ?_
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [hsym a l]
      _ = ∑ a : Idx, ∑ l : Idx, gInv a l * D a p l := rfl
  have hsplit :
      (∑ a : Idx, ∑ l : Idx, gInv a l * (D p a l + D a p l - D l p a))
        = S₁ + S₂ - S₃ := by
    unfold S₁ S₂ S₃
    simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  calc
    (∑ a : Idx,
        (1 / 2 : ℝ) *
          ∑ l : Idx, gInv a l * (D p a l + D a p l - D l p a))
        =
      (1 / 2 : ℝ) *
        (∑ a : Idx, ∑ l : Idx, gInv a l * (D p a l + D a p l - D l p a)) := by
          rw [Finset.mul_sum]
    _ = (1 / 2 : ℝ) * (S₁ + S₂ - S₃) := by
          rw [hsplit]
    _ = (1 / 2 : ℝ) * S₁ := by
          rw [hS₃]
          ring
    _ = (1 / 2 : ℝ) * ∑ i : Idx, ∑ j : Idx, gInv i j * D p i j := rfl







omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] in
omit [InnerProductSpace ℝ E] in
theorem lcTrace_halfTrace
    (g : SmoothRiemannianMetric I M) (x : M)
    (p : Fin (Module.finrank ℝ E)) :
    (∑ a : Fin (Module.finrank ℝ E),
        chartChristoffel (I := I) g x p a a (extChartAt I x x))
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
  have hsymm_y₀ : (extChartAt I x).symm y₀ = x := by
    simp only [y₀]
    rw [(extChartAt I x).left_inv (mem_extChartAt_source (I := I) x)]
  let gInv : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun i j => chartInvGramMatrix (I := I) g x x i j
  let D :
      Fin (Module.finrank ℝ E) →
        Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun r i j =>
      partialDeriv (E := E) r (chartGramOnE (I := I) g x i j) y₀
  have hsym : ∀ i j : Fin (Module.finrank ℝ E), gInv i j = gInv j i := by
    intro i j
    exact (chartInvGramMatrix_symm (I := I) g x x j i)
  have hformula :
      ∀ a : Fin (Module.finrank ℝ E),
        chartChristoffel (I := I) g x p a a y₀ =
          (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
            gInv a l * (D p a l + D a p l - D l p a) := by
    intro a
    rw [chartChristoffel_def]
    simp only [gInv, D, hsymm_y₀]
    refine congrArg (fun t => (1 / 2 : ℝ) * t) ?_
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [show chartGramOnE (I := I) g x l a = chartGramOnE (I := I) g x a l from
          funext fun y => chartGramOnE_symm (I := I) g x l a y,
        show chartGramOnE (I := I) g x l p = chartGramOnE (I := I) g x p l from
          funext fun y => chartGramOnE_symm (I := I) g x l p y]
  calc
    (∑ a : Fin (Module.finrank ℝ E),
        chartChristoffel (I := I) g x p a a y₀)
        =
      ∑ a : Fin (Module.finrank ℝ E),
        (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
          gInv a l * (D p a l + D a p l - D l p a) := by
          refine Finset.sum_congr rfl fun a _ => hformula a
    _ =
      (1 / 2 : ℝ) * ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E), gInv i j * D p i j := by
          exact traceChristoffelAlg gInv D hsym p
    _ =
      (1 / 2 : ℝ) *
        ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g x x i j *
              partialDeriv (E := E) p
                (fun y : E =>
                  chartGramMatrix (I := I) g x ((extChartAt I x).symm y) i j)
                y₀ := rfl







omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] in
omit [InnerProductSpace ℝ E] in
theorem lcTrace_logDensity
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M)
    (p : Fin (Module.finrank ℝ E)) :
    partialDeriv (E := E) p
        (chartDensityOnE (I := I) g x) (extChartAt I x x) /
      chartDensity (I := I) g x x
      =
    ∑ a : Fin (Module.finrank ℝ E),
      chartChristoffel (I := I) g x p a a (extChartAt I x x) := by
  have hρ :
      chartDensityOnE (I := I) g x (extChartAt I x x) =
        chartDensity (I := I) g x x := by
    change chartDensity (I := I) g x ((extChartAt I x).symm (extChartAt I x x)) =
      chartDensity (I := I) g x x
    rw [(extChartAt I x).left_inv (mem_extChartAt_source (I := I) x)]
  calc
    partialDeriv (E := E) p
        (chartDensityOnE (I := I) g x) (extChartAt I x x) /
      chartDensity (I := I) g x x
        =
      partialDeriv (E := E) p
        (chartDensityOnE (I := I) g x) (extChartAt I x x) /
      chartDensityOnE (I := I) g x (extChartAt I x x) := by
          rw [hρ]
    _ =
      (1 / 2 : ℝ) *
        ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g x x i j *
              partialDeriv (E := E) p
                (fun y : E =>
                  chartGramMatrix (I := I) g x ((extChartAt I x).symm y) i j)
                (extChartAt I x x) := by
          exact
            chartDensityOnE_partial_div_eq_half_trace_invGram_partialGram
              (I := I) g x p
    _ =
      ∑ a : Fin (Module.finrank ℝ E),
        chartChristoffel (I := I) g x p a a (extChartAt I x x) := by
          exact (lcTrace_halfTrace (I := I) g x p).symm

end DifferentialGeometry.Integral.Connection
