import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciSecondOrderPart
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.InvGramPerturbation
import DifferentialGeometry.Analysis.Parabolic.PrincipalSymbol


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

section InvGramBridge

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma chartInvGramOnE_extChartAt_self (g : SmoothRiemannianMetric I M) (x : M)
    (j l : Fin (Module.finrank ℝ E)) :
    chartInvGramOnE (I := I) g x j l (extChartAt I x x) =
      chartInvGramMatrix (I := I) g x x j l := by
  rw [chartInvGramOnE_def, extChartAt_to_inv]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma chartInvGramMatrix_self_symm (g : SmoothRiemannianMetric I M) (x : M)
    (j l : Fin (Module.finrank ℝ E)) :
    chartInvGramMatrix (I := I) g x x j l =
      chartInvGramMatrix (I := I) g x x l j := by
  have hHerm : (chartInvGramMatrix (I := I) g x x).IsHermitian := by
    unfold chartInvGramMatrix
    exact (chartGramMatrix_isHermitian (I := I) g x x).inv
  have hentry := hHerm.apply l j
  rwa [star_trivial] at hentry

end InvGramBridge

section FibreForm

def formComp (x : M)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (c d : Fin (Module.finrank ℝ E)) : ℝ :=
  t ((chartModelBasis E) c) ((chartModelBasis E) d)

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
@[simp] lemma formComp_def (x : M)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (c d : Fin (Module.finrank ℝ E)) :
    formComp (I := I) x t c d =
      t ((chartModelBasis E) c) ((chartModelBasis E) d) := rfl

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
@[simp] lemma formComp_zero (x : M) (c d : Fin (Module.finrank ℝ E)) :
    formComp (I := I) x
      (0 : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ) c d = 0 := rfl

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma formComp_add (x : M)
    (t t' : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (c d : Fin (Module.finrank ℝ E)) :
    formComp (I := I) x (t + t') c d =
      formComp (I := I) x t c d + formComp (I := I) x t' c d := by
  simp [formComp]

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma formComp_smul (x : M) (a : ℝ)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (c d : Fin (Module.finrank ℝ E)) :
    formComp (I := I) x (a • t) c d = a * formComp (I := I) x t c d := by
  simp [formComp]

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma formComp_symm (x : M)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (ht : ∀ v w, t v w = t w v) (c d : Fin (Module.finrank ℝ E)) :
    formComp (I := I) x t c d = formComp (I := I) x t d c := by
  rw [formComp_def, formComp_def, ht]

def formMetricTrace (g : SmoothRiemannianMetric I M) (x : M)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ) : ℝ :=
  ∑ m : Fin (Module.finrank ℝ E),
    ∑ n : Fin (Module.finrank ℝ E),
      chartInvGramMatrix (I := I) g x x m n * formComp (I := I) x t m n

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
@[simp] lemma formMetricTrace_def (g : SmoothRiemannianMetric I M) (x : M)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ) :
    formMetricTrace (I := I) g x t =
      ∑ m : Fin (Module.finrank ℝ E),
        ∑ n : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g x x m n * formComp (I := I) x t m n := rfl

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
@[simp] lemma formMetricTrace_zero (g : SmoothRiemannianMetric I M) (x : M) :
    formMetricTrace (I := I) g x
      (0 : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ) = 0 := by
  simp [formMetricTrace]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma formMetricTrace_add (g : SmoothRiemannianMetric I M) (x : M)
    (t t' : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ) :
    formMetricTrace (I := I) g x (t + t') =
      formMetricTrace (I := I) g x t + formMetricTrace (I := I) g x t' := by
  rw [formMetricTrace_def, formMetricTrace_def, formMetricTrace_def,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [formComp_add]
  ring

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma formMetricTrace_smul (g : SmoothRiemannianMetric I M) (x : M) (a : ℝ)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ) :
    formMetricTrace (I := I) g x (a • t) = a * formMetricTrace (I := I) g x t := by
  rw [formMetricTrace_def, formMetricTrace_def, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [formComp_smul]
  ring

def raisedFormContraction (g : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (k : Fin (Module.finrank ℝ E)) : ℝ :=
  ∑ l : Fin (Module.finrank ℝ E),
    raisedCovectorComp (I := I) g x ξ l * formComp (I := I) x t l k

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
@[simp] lemma raisedFormContraction_def (g : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (k : Fin (Module.finrank ℝ E)) :
    raisedFormContraction (I := I) g x ξ t k =
      ∑ l : Fin (Module.finrank ℝ E),
        raisedCovectorComp (I := I) g x ξ l * formComp (I := I) x t l k := rfl

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
@[simp] lemma raisedFormContraction_zero (g : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (k : Fin (Module.finrank ℝ E)) :
    raisedFormContraction (I := I) g x ξ
      (0 : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ) k = 0 := by
  simp [raisedFormContraction]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma raisedFormContraction_add (g : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (t t' : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (k : Fin (Module.finrank ℝ E)) :
    raisedFormContraction (I := I) g x ξ (t + t') k =
      raisedFormContraction (I := I) g x ξ t k +
        raisedFormContraction (I := I) g x ξ t' k := by
  rw [raisedFormContraction_def, raisedFormContraction_def, raisedFormContraction_def,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [formComp_add]
  ring

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma raisedFormContraction_smul (g : SmoothRiemannianMetric I M) (x : M) (ξ : E) (a : ℝ)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (k : Fin (Module.finrank ℝ E)) :
    raisedFormContraction (I := I) g x ξ (a • t) k =
      a * raisedFormContraction (I := I) g x ξ t k := by
  rw [raisedFormContraction_def, raisedFormContraction_def, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [formComp_smul]
  ring

def raisedFormContractionSnd (g : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (i : Fin (Module.finrank ℝ E)) : ℝ :=
  ∑ j : Fin (Module.finrank ℝ E),
    raisedCovectorComp (I := I) g x ξ j * formComp (I := I) x t i j

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
@[simp] lemma raisedFormContractionSnd_def (g : SmoothRiemannianMetric I M) (x : M)
    (ξ : E) (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (i : Fin (Module.finrank ℝ E)) :
    raisedFormContractionSnd (I := I) g x ξ t i =
      ∑ j : Fin (Module.finrank ℝ E),
        raisedCovectorComp (I := I) g x ξ j * formComp (I := I) x t i j := rfl

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
@[simp] lemma raisedFormContractionSnd_zero (g : SmoothRiemannianMetric I M) (x : M)
    (ξ : E) (i : Fin (Module.finrank ℝ E)) :
    raisedFormContractionSnd (I := I) g x ξ
      (0 : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ) i = 0 := by
  simp [raisedFormContractionSnd]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma raisedFormContractionSnd_add (g : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (t t' : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (i : Fin (Module.finrank ℝ E)) :
    raisedFormContractionSnd (I := I) g x ξ (t + t') i =
      raisedFormContractionSnd (I := I) g x ξ t i +
        raisedFormContractionSnd (I := I) g x ξ t' i := by
  rw [raisedFormContractionSnd_def, raisedFormContractionSnd_def,
    raisedFormContractionSnd_def, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [formComp_add]
  ring

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma raisedFormContractionSnd_smul (g : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (a : ℝ) (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (i : Fin (Module.finrank ℝ E)) :
    raisedFormContractionSnd (I := I) g x ξ (a • t) i =
      a * raisedFormContractionSnd (I := I) g x ξ t i := by
  rw [raisedFormContractionSnd_def, raisedFormContractionSnd_def, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [formComp_smul]
  ring

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma raisedFormContractionSnd_eq_of_symm (g : SmoothRiemannianMetric I M) (x : M)
    (ξ : E) (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (ht : ∀ v w, t v w = t w v) (i : Fin (Module.finrank ℝ E)) :
    raisedFormContractionSnd (I := I) g x ξ t i =
      raisedFormContraction (I := I) g x ξ t i := by
  rw [raisedFormContractionSnd_def, raisedFormContraction_def]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [formComp_symm (I := I) x t ht i j]

end FibreForm

section SymbolComponent

def ricciSymbolComp (g : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (i k : Fin (Module.finrank ℝ E)) : ℝ :=
  (1 / 2 : ℝ) * ∑ j : Fin (Module.finrank ℝ E),
    ∑ l : Fin (Module.finrank ℝ E),
      chartInvGramOnE (I := I) g x j l (extChartAt I x x) *
        ((chartModelBasis E).repr ξ j * (chartModelBasis E).repr ξ i *
            formComp (I := I) x t l k +
          (chartModelBasis E).repr ξ k * (chartModelBasis E).repr ξ l *
            formComp (I := I) x t i j -
          (chartModelBasis E).repr ξ j * (chartModelBasis E).repr ξ l *
            formComp (I := I) x t i k -
          (chartModelBasis E).repr ξ k * (chartModelBasis E).repr ξ i *
            formComp (I := I) x t l j)

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
@[simp] lemma ricciSymbolComp_def (g : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (i k : Fin (Module.finrank ℝ E)) :
    ricciSymbolComp (I := I) g x ξ t i k =
      (1 / 2 : ℝ) * ∑ j : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g x j l (extChartAt I x x) *
            ((chartModelBasis E).repr ξ j * (chartModelBasis E).repr ξ i *
                formComp (I := I) x t l k +
              (chartModelBasis E).repr ξ k * (chartModelBasis E).repr ξ l *
                formComp (I := I) x t i j -
              (chartModelBasis E).repr ξ j * (chartModelBasis E).repr ξ l *
                formComp (I := I) x t i k -
              (chartModelBasis E).repr ξ k * (chartModelBasis E).repr ξ i *
                formComp (I := I) x t l j) := rfl

end SymbolComponent

section ClosedForm

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma sum_term_one (g : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (i k : Fin (Module.finrank ℝ E)) :
    ∑ j : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g x x j l *
            ((chartModelBasis E).repr ξ j * (chartModelBasis E).repr ξ i *
              formComp (I := I) x t l k) =
      (chartModelBasis E).repr ξ i *
        raisedFormContraction (I := I) g x ξ t k := by
  calc
    ∑ j : Fin (Module.finrank ℝ E),
          ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g x x j l *
              ((chartModelBasis E).repr ξ j * (chartModelBasis E).repr ξ i *
                formComp (I := I) x t l k)
      = ∑ l : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g x x j l *
              ((chartModelBasis E).repr ξ j * (chartModelBasis E).repr ξ i *
                formComp (I := I) x t l k) := Finset.sum_comm
    _ = ∑ l : Fin (Module.finrank ℝ E),
          (chartModelBasis E).repr ξ i *
            (raisedCovectorComp (I := I) g x ξ l * formComp (I := I) x t l k) := by
        refine Finset.sum_congr rfl (fun l _ => ?_)
        rw [raisedCovectorComp_def, Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [chartInvGramMatrix_self_symm (I := I) g x j l]
        ring
    _ = (chartModelBasis E).repr ξ i *
          raisedFormContraction (I := I) g x ξ t k := by
        rw [raisedFormContraction_def, Finset.mul_sum]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma sum_term_two (g : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (i k : Fin (Module.finrank ℝ E)) :
    ∑ j : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g x x j l *
            ((chartModelBasis E).repr ξ k * (chartModelBasis E).repr ξ l *
              formComp (I := I) x t i j) =
      (chartModelBasis E).repr ξ k *
        raisedFormContractionSnd (I := I) g x ξ t i := by
  calc
    ∑ j : Fin (Module.finrank ℝ E),
          ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g x x j l *
              ((chartModelBasis E).repr ξ k * (chartModelBasis E).repr ξ l *
                formComp (I := I) x t i j)
      = ∑ j : Fin (Module.finrank ℝ E),
          (chartModelBasis E).repr ξ k *
            (raisedCovectorComp (I := I) g x ξ j * formComp (I := I) x t i j) := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [raisedCovectorComp_def, Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun l _ => ?_)
        ring
    _ = (chartModelBasis E).repr ξ k *
          raisedFormContractionSnd (I := I) g x ξ t i := by
        rw [raisedFormContractionSnd_def, Finset.mul_sum]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma sum_term_three (g : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (i k : Fin (Module.finrank ℝ E)) :
    ∑ j : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g x x j l *
            ((chartModelBasis E).repr ξ j * (chartModelBasis E).repr ξ l *
              formComp (I := I) x t i k) =
      metricCovectorNormSq (I := I) g x ξ * formComp (I := I) x t i k := by
  rw [metricCovectorNormSq_def, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  ring

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma sum_term_four (g : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (i k : Fin (Module.finrank ℝ E)) :
    ∑ j : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g x x j l *
            ((chartModelBasis E).repr ξ k * (chartModelBasis E).repr ξ i *
              formComp (I := I) x t l j) =
      (chartModelBasis E).repr ξ k * (chartModelBasis E).repr ξ i *
        formMetricTrace (I := I) g x t := by
  calc
    ∑ j : Fin (Module.finrank ℝ E),
          ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g x x j l *
              ((chartModelBasis E).repr ξ k * (chartModelBasis E).repr ξ i *
                formComp (I := I) x t l j)
      = ∑ m : Fin (Module.finrank ℝ E),
          ∑ n : Fin (Module.finrank ℝ E),
            (chartModelBasis E).repr ξ k * (chartModelBasis E).repr ξ i *
              (chartInvGramMatrix (I := I) g x x m n *
                formComp (I := I) x t m n) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun m _ => ?_)
        refine Finset.sum_congr rfl (fun n _ => ?_)
        rw [chartInvGramMatrix_self_symm (I := I) g x n m]
        ring
    _ = (chartModelBasis E).repr ξ k * (chartModelBasis E).repr ξ i *
          formMetricTrace (I := I) g x t := by
        rw [formMetricTrace_def, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun m _ => ?_)
        rw [Finset.mul_sum]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma ricciSymbol_doubleSum_split (g : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (i k : Fin (Module.finrank ℝ E)) :
    ∑ j : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g x x j l *
            ((chartModelBasis E).repr ξ j * (chartModelBasis E).repr ξ i *
                formComp (I := I) x t l k +
              (chartModelBasis E).repr ξ k * (chartModelBasis E).repr ξ l *
                formComp (I := I) x t i j -
              (chartModelBasis E).repr ξ j * (chartModelBasis E).repr ξ l *
                formComp (I := I) x t i k -
              (chartModelBasis E).repr ξ k * (chartModelBasis E).repr ξ i *
                formComp (I := I) x t l j) =
      (∑ j : Fin (Module.finrank ℝ E),
          ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g x x j l *
              ((chartModelBasis E).repr ξ j * (chartModelBasis E).repr ξ i *
                formComp (I := I) x t l k)) +
      (∑ j : Fin (Module.finrank ℝ E),
          ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g x x j l *
              ((chartModelBasis E).repr ξ k * (chartModelBasis E).repr ξ l *
                formComp (I := I) x t i j)) -
      (∑ j : Fin (Module.finrank ℝ E),
          ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g x x j l *
              ((chartModelBasis E).repr ξ j * (chartModelBasis E).repr ξ l *
                formComp (I := I) x t i k)) -
      (∑ j : Fin (Module.finrank ℝ E),
          ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g x x j l *
              ((chartModelBasis E).repr ξ k * (chartModelBasis E).repr ξ i *
                formComp (I := I) x t l j)) := by
  have hdist : ∀ j l : Fin (Module.finrank ℝ E),
      chartInvGramMatrix (I := I) g x x j l *
          ((chartModelBasis E).repr ξ j * (chartModelBasis E).repr ξ i *
              formComp (I := I) x t l k +
            (chartModelBasis E).repr ξ k * (chartModelBasis E).repr ξ l *
              formComp (I := I) x t i j -
            (chartModelBasis E).repr ξ j * (chartModelBasis E).repr ξ l *
              formComp (I := I) x t i k -
            (chartModelBasis E).repr ξ k * (chartModelBasis E).repr ξ i *
              formComp (I := I) x t l j) =
        chartInvGramMatrix (I := I) g x x j l *
            ((chartModelBasis E).repr ξ j * (chartModelBasis E).repr ξ i *
              formComp (I := I) x t l k) +
          chartInvGramMatrix (I := I) g x x j l *
            ((chartModelBasis E).repr ξ k * (chartModelBasis E).repr ξ l *
              formComp (I := I) x t i j) -
          chartInvGramMatrix (I := I) g x x j l *
            ((chartModelBasis E).repr ξ j * (chartModelBasis E).repr ξ l *
              formComp (I := I) x t i k) -
          chartInvGramMatrix (I := I) g x x j l *
            ((chartModelBasis E).repr ξ k * (chartModelBasis E).repr ξ i *
              formComp (I := I) x t l j) := fun j l => by ring
  have hrow : ∀ j : Fin (Module.finrank ℝ E),
      (∑ l : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g x x j l *
            ((chartModelBasis E).repr ξ j * (chartModelBasis E).repr ξ i *
                formComp (I := I) x t l k +
              (chartModelBasis E).repr ξ k * (chartModelBasis E).repr ξ l *
                formComp (I := I) x t i j -
              (chartModelBasis E).repr ξ j * (chartModelBasis E).repr ξ l *
                formComp (I := I) x t i k -
              (chartModelBasis E).repr ξ k * (chartModelBasis E).repr ξ i *
                formComp (I := I) x t l j)) =
        (∑ l : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g x x j l *
              ((chartModelBasis E).repr ξ j * (chartModelBasis E).repr ξ i *
                formComp (I := I) x t l k)) +
          (∑ l : Fin (Module.finrank ℝ E),
              chartInvGramMatrix (I := I) g x x j l *
                ((chartModelBasis E).repr ξ k * (chartModelBasis E).repr ξ l *
                  formComp (I := I) x t i j)) -
          (∑ l : Fin (Module.finrank ℝ E),
              chartInvGramMatrix (I := I) g x x j l *
                ((chartModelBasis E).repr ξ j * (chartModelBasis E).repr ξ l *
                  formComp (I := I) x t i k)) -
          (∑ l : Fin (Module.finrank ℝ E),
              chartInvGramMatrix (I := I) g x x j l *
                ((chartModelBasis E).repr ξ k * (chartModelBasis E).repr ξ i *
                  formComp (I := I) x t l j)) := by
    intro j
    rw [Finset.sum_congr rfl (fun l (_ : l ∈ Finset.univ) => hdist j l),
      Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => hrow j),
    Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem ricciSymbolComp_eq_closedForm (g : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (i k : Fin (Module.finrank ℝ E)) :
    ricciSymbolComp (I := I) g x ξ t i k =
      (1 / 2 : ℝ) * ((chartModelBasis E).repr ξ i *
          raisedFormContraction (I := I) g x ξ t k) +
        (1 / 2 : ℝ) * ((chartModelBasis E).repr ξ k *
          raisedFormContractionSnd (I := I) g x ξ t i) -
        (1 / 2 : ℝ) * (metricCovectorNormSq (I := I) g x ξ *
          formComp (I := I) x t i k) -
        (1 / 2 : ℝ) * ((chartModelBasis E).repr ξ i *
          (chartModelBasis E).repr ξ k * formMetricTrace (I := I) g x t) := by
  rw [ricciSymbolComp_def]
  have hgram : ∀ j l : Fin (Module.finrank ℝ E),
      chartInvGramOnE (I := I) g x j l (extChartAt I x x) =
        chartInvGramMatrix (I := I) g x x j l :=
    fun j l => chartInvGramOnE_extChartAt_self (I := I) g x j l
  rw [show (∑ j : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g x j l (extChartAt I x x) *
            ((chartModelBasis E).repr ξ j * (chartModelBasis E).repr ξ i *
                formComp (I := I) x t l k +
              (chartModelBasis E).repr ξ k * (chartModelBasis E).repr ξ l *
                formComp (I := I) x t i j -
              (chartModelBasis E).repr ξ j * (chartModelBasis E).repr ξ l *
                formComp (I := I) x t i k -
              (chartModelBasis E).repr ξ k * (chartModelBasis E).repr ξ i *
                formComp (I := I) x t l j)) =
      (∑ j : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g x x j l *
            ((chartModelBasis E).repr ξ j * (chartModelBasis E).repr ξ i *
                formComp (I := I) x t l k +
              (chartModelBasis E).repr ξ k * (chartModelBasis E).repr ξ l *
                formComp (I := I) x t i j -
              (chartModelBasis E).repr ξ j * (chartModelBasis E).repr ξ l *
                formComp (I := I) x t i k -
              (chartModelBasis E).repr ξ k * (chartModelBasis E).repr ξ i *
                formComp (I := I) x t l j)) from by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [hgram j l]]
  rw [ricciSymbol_doubleSum_split (I := I) g x ξ t i k,
    sum_term_one (I := I) g x ξ t i k, sum_term_two (I := I) g x ξ t i k,
    sum_term_three (I := I) g x ξ t i k, sum_term_four (I := I) g x ξ t i k]
  ring

end ClosedForm

section Linearity

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem ricciSymbolComp_add (g : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (t t' : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (i k : Fin (Module.finrank ℝ E)) :
    ricciSymbolComp (I := I) g x ξ (t + t') i k =
      ricciSymbolComp (I := I) g x ξ t i k +
        ricciSymbolComp (I := I) g x ξ t' i k := by
  rw [ricciSymbolComp_eq_closedForm (I := I) g x ξ (t + t') i k,
    ricciSymbolComp_eq_closedForm (I := I) g x ξ t i k,
    ricciSymbolComp_eq_closedForm (I := I) g x ξ t' i k,
    raisedFormContraction_add, raisedFormContractionSnd_add, formComp_add,
    formMetricTrace_add]
  ring

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem ricciSymbolComp_smul (g : SmoothRiemannianMetric I M) (x : M) (ξ : E) (a : ℝ)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (i k : Fin (Module.finrank ℝ E)) :
    ricciSymbolComp (I := I) g x ξ (a • t) i k =
      a * ricciSymbolComp (I := I) g x ξ t i k := by
  rw [ricciSymbolComp_eq_closedForm (I := I) g x ξ (a • t) i k,
    ricciSymbolComp_eq_closedForm (I := I) g x ξ t i k,
    raisedFormContraction_smul, raisedFormContractionSnd_smul, formComp_smul,
    formMetricTrace_smul]
  ring

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
@[simp] theorem ricciSymbolComp_zero (g : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (i k : Fin (Module.finrank ℝ E)) :
    ricciSymbolComp (I := I) g x ξ
      (0 : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ) i k = 0 := by
  rw [ricciSymbolComp_eq_closedForm, raisedFormContraction_zero,
    raisedFormContractionSnd_zero, formComp_zero, formMetricTrace_zero]
  ring

end Linearity

section Symmetry

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem ricciSymbolComp_symm (g : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (ht : ∀ v w, t v w = t w v) (i k : Fin (Module.finrank ℝ E)) :
    ricciSymbolComp (I := I) g x ξ t i k =
      ricciSymbolComp (I := I) g x ξ t k i := by
  rw [ricciSymbolComp_eq_closedForm (I := I) g x ξ t i k,
    ricciSymbolComp_eq_closedForm (I := I) g x ξ t k i]
  rw [raisedFormContractionSnd_eq_of_symm (I := I) g x ξ t ht i,
    raisedFormContractionSnd_eq_of_symm (I := I) g x ξ t ht k,
    formComp_symm (I := I) x t ht i k]
  ring

end Symmetry

end RicciLinearization
end DeTurck
end PDE
end DifferentialGeometry
