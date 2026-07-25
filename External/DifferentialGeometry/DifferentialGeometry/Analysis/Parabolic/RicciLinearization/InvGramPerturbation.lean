import DifferentialGeometry.Geometry.Flow.DeTurckOperator
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Const


noncomputable section

open Set Function
open scoped Topology ContDiff Matrix Manifold

namespace DifferentialGeometry
namespace PDE
namespace DeTurck
namespace RicciLinearization

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

section PartialDerivAlgebra

variable {i : Fin (Module.finrank ℝ E)} {y : E}

omit [NeZero (Module.finrank ℝ E)] in
lemma partialDeriv_add (u v : E → ℝ)
    (hu : DifferentiableAt ℝ u y) (hv : DifferentiableAt ℝ v y) :
    partialDeriv (E := E) i (fun y => u y + v y) y =
      partialDeriv (E := E) i u y + partialDeriv (E := E) i v y := by
  unfold partialDeriv
  rw [fderiv_fun_add hu hv]
  rfl

omit [NeZero (Module.finrank ℝ E)] in
lemma partialDeriv_sub (u v : E → ℝ)
    (hu : DifferentiableAt ℝ u y) (hv : DifferentiableAt ℝ v y) :
    partialDeriv (E := E) i (fun y => u y - v y) y =
      partialDeriv (E := E) i u y - partialDeriv (E := E) i v y := by
  unfold partialDeriv
  rw [fderiv_fun_sub hu hv]
  rfl

omit [NeZero (Module.finrank ℝ E)] in
lemma partialDeriv_smul (c u : E → ℝ)
    (hc : DifferentiableAt ℝ c y) (hu : DifferentiableAt ℝ u y) :
    partialDeriv (E := E) i (fun y => c y • u y) y =
      c y • partialDeriv (E := E) i u y + partialDeriv (E := E) i c y • u y := by
  unfold partialDeriv
  rw [fderiv_fun_smul hc hu]
  simp [ContinuousLinearMap.smulRight_apply, smul_eq_mul, mul_comm]

omit [NeZero (Module.finrank ℝ E)] in
lemma partialDeriv_const_smul (c : ℝ) (u : E → ℝ)
    (hu : DifferentiableAt ℝ u y) :
    partialDeriv (E := E) i (fun y => c • u y) y =
      c • partialDeriv (E := E) i u y := by
  unfold partialDeriv
  rw [fderiv_fun_const_smul hu c]
  rfl

omit [NeZero (Module.finrank ℝ E)] in
lemma partialDeriv_const_mul (c : ℝ) (u : E → ℝ)
    (hu : DifferentiableAt ℝ u y) :
    partialDeriv (E := E) i (fun y => c * u y) y =
      c * partialDeriv (E := E) i u y := by
  unfold partialDeriv
  rw [fderiv_const_mul hu c]
  simp [ContinuousLinearMap.smul_apply, smul_eq_mul]

omit [NeZero (Module.finrank ℝ E)] in
lemma partialDeriv_mul (u v : E → ℝ)
    (hu : DifferentiableAt ℝ u y) (hv : DifferentiableAt ℝ v y) :
    partialDeriv (E := E) i (fun y => u y * v y) y =
      partialDeriv (E := E) i u y * v y + u y * partialDeriv (E := E) i v y := by
  unfold partialDeriv
  rw [fderiv_fun_mul hu hv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

omit [NeZero (Module.finrank ℝ E)] in
lemma partialDeriv_sum {ι : Type*} (s : Finset ι) (A : ι → E → ℝ)
    (hA : ∀ k ∈ s, DifferentiableAt ℝ (A k) y) :
    partialDeriv (E := E) i (fun y => ∑ k ∈ s, A k y) y =
      ∑ k ∈ s, partialDeriv (E := E) i (A k) y := by
  unfold partialDeriv
  rw [fderiv_fun_sum hA]
  rw [ContinuousLinearMap.sum_apply]

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma partialDeriv_const (c : ℝ) :
    partialDeriv (E := E) i (fun _ : E => c) y = 0 := by
  unfold partialDeriv
  rw [show (fun _ : E => c) = Function.const E c from rfl, fderiv_const]
  rfl

end PartialDerivAlgebra

structure ChartMetricPerturbation (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] where

  toFun : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → (E → ℝ)

  symm' : ∀ i j y, toFun i j y = toFun j i y

  smooth' : ∀ i j, ContDiff ℝ ∞ (toFun i j)

namespace ChartMetricPerturbation

instance : CoeFun (ChartMetricPerturbation E)
    (fun _ => Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → (E → ℝ)) :=
  ⟨ChartMetricPerturbation.toFun⟩

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma coe_mk
    (f : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → (E → ℝ))
    (hsymm : ∀ i j y, f i j y = f j i y) (hsmooth : ∀ i j, ContDiff ℝ ∞ (f i j)) :
    ⇑(ChartMetricPerturbation.mk f hsymm hsmooth) = f := rfl

omit [NeZero (Module.finrank ℝ E)] in
lemma symm (h : ChartMetricPerturbation E) (i j : Fin (Module.finrank ℝ E)) (y : E) :
    h i j y = h j i y := h.symm' i j y

omit [NeZero (Module.finrank ℝ E)] in
lemma symm_fun (h : ChartMetricPerturbation E) (i j : Fin (Module.finrank ℝ E)) :
    h i j = h j i := funext (h.symm i j)

omit [NeZero (Module.finrank ℝ E)] in
lemma smooth (h : ChartMetricPerturbation E) (i j : Fin (Module.finrank ℝ E)) :
    ContDiff ℝ ∞ (h i j) := h.smooth' i j

omit [NeZero (Module.finrank ℝ E)] in
lemma differentiableAt (h : ChartMetricPerturbation E)
    (i j : Fin (Module.finrank ℝ E)) (y : E) :
    DifferentiableAt ℝ (h i j) y :=
  ((h.smooth i j).differentiable (by simp)).differentiableAt

instance : Zero (ChartMetricPerturbation E) :=
  ⟨{ toFun := fun _ _ _ => 0
     symm' := fun _ _ _ => rfl
     smooth' := fun _ _ => contDiff_const }⟩

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma zero_apply (i j : Fin (Module.finrank ℝ E)) (y : E) :
    (0 : ChartMetricPerturbation E) i j y = 0 := rfl

omit [NeZero (Module.finrank ℝ E)] in
@[ext] lemma ext {h h' : ChartMetricPerturbation E}
    (hyp : ∀ i j, (h i j) = (h' i j)) : h = h' := by
  cases h; cases h'; congr 1; funext i j; exact hyp i j

end ChartMetricPerturbation

section TraceAndRaising

def raisedCovectorComp (g : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (m : Fin (Module.finrank ℝ E)) : ℝ :=
  ∑ n : Fin (Module.finrank ℝ E),
    chartInvGramMatrix (I := I) g x x m n * (chartModelBasis E).repr ξ n

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
@[simp] lemma raisedCovectorComp_def (g : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (m : Fin (Module.finrank ℝ E)) :
    raisedCovectorComp (I := I) g x ξ m =
      ∑ n : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g x x m n * (chartModelBasis E).repr ξ n := rfl

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
@[simp] lemma raisedCovectorComp_zero (g : SmoothRiemannianMetric I M) (x : M)
    (m : Fin (Module.finrank ℝ E)) :
    raisedCovectorComp (I := I) g x (0 : E) m = 0 := by
  simp [raisedCovectorComp]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma sum_raisedCovectorComp_mul_repr
    (g : SmoothRiemannianMetric I M) (x : M) (ξ : E) :
    ∑ m : Fin (Module.finrank ℝ E),
        raisedCovectorComp (I := I) g x ξ m * (chartModelBasis E).repr ξ m =
      metricCovectorNormSq (I := I) g x ξ := by
  rw [metricCovectorNormSq_def]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [raisedCovectorComp_def, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  ring

def metricTrace (g : SmoothRiemannianMetric I M) (x : M)
    (h : ChartMetricPerturbation E) : ℝ :=
  ∑ m : Fin (Module.finrank ℝ E),
    ∑ n : Fin (Module.finrank ℝ E),
      chartInvGramMatrix (I := I) g x x m n * h m n (extChartAt I x x)

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
@[simp] lemma metricTrace_def (g : SmoothRiemannianMetric I M) (x : M)
    (h : ChartMetricPerturbation E) :
    metricTrace (I := I) g x h =
      ∑ m : Fin (Module.finrank ℝ E),
        ∑ n : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g x x m n * h m n (extChartAt I x x) := rfl

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
@[simp] lemma metricTrace_zero (g : SmoothRiemannianMetric I M) (x : M) :
    metricTrace (I := I) g x (0 : ChartMetricPerturbation E) = 0 := by
  simp [metricTrace]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma metricTrace_congr (g : SmoothRiemannianMetric I M) (x : M)
    {h h' : ChartMetricPerturbation E}
    (hyp : ∀ m n, h m n (extChartAt I x x) = h' m n (extChartAt I x x)) :
    metricTrace (I := I) g x h = metricTrace (I := I) g x h' := by
  rw [metricTrace_def, metricTrace_def]
  exact Finset.sum_congr rfl (fun m _ =>
    Finset.sum_congr rfl (fun n _ => by rw [hyp m n]))

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma metricTrace_eq_sum (g : SmoothRiemannianMetric I M) (x : M)
    (h : ChartMetricPerturbation E) :
    metricTrace (I := I) g x h =
      ∑ p : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g x x p.1 p.2 *
          h p.1 p.2 (extChartAt I x x) := by
  rw [metricTrace_def, ← Finset.sum_product', Finset.univ_product_univ]

end TraceAndRaising

section InvGramPerturbation

def invGramPerturbation (g : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (l m : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  -∑ a : Fin (Module.finrank ℝ E),
    ∑ b : Fin (Module.finrank ℝ E),
      chartInvGramOnE (I := I) g α l a y *
        chartInvGramOnE (I := I) g α b m y * h a b y

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
@[simp] lemma invGramPerturbation_def (g : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (l m : Fin (Module.finrank ℝ E)) (y : E) :
    invGramPerturbation (I := I) g α h l m y =
      -∑ a : Fin (Module.finrank ℝ E),
        ∑ b : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α l a y *
            chartInvGramOnE (I := I) g α b m y * h a b y := rfl

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
@[simp] lemma invGramPerturbation_zero (g : SmoothRiemannianMetric I M) (α : M)
    (l m : Fin (Module.finrank ℝ E)) (y : E) :
    invGramPerturbation (I := I) g α (0 : ChartMetricPerturbation E) l m y = 0 := by
  simp [invGramPerturbation]

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma invGramPerturbation_symm (g : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (l m : Fin (Module.finrank ℝ E)) (y : E) :
    invGramPerturbation (I := I) g α h l m y =
      invGramPerturbation (I := I) g α h m l y := by
  rw [invGramPerturbation_def, invGramPerturbation_def]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [chartInvGramOnE_symm (I := I) g α l b y,
    chartInvGramOnE_symm (I := I) g α a m y, h.symm b a y]
  ring

end InvGramPerturbation

end RicciLinearization
end DeTurck
end PDE
end DifferentialGeometry
