import DifferentialGeometry.Geometry.Connection.TensorNabla.CotangentExtension
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.CovGradParallelNaturality
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.CovGradCovDerivCommutation
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.TensorMetricCompatible
import DifferentialGeometry.Geometry.Metric.TensorInner.CotangentRiemannian
import DifferentialGeometry.Analysis.Spectral.Tensor.Variational.CovDerivPointwise


noncomputable section

open Bundle Manifold Set Filter FiberBundle Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open Tensor0SNabla
open TensorRSNabla
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

def ccTensorOneForm (g : SmoothRiemannianMetric I M) (σ : SmoothCcTensor g 0 1) :
    Π b : M, TangentSpace I b →L[ℝ] ℝ :=
  fun b => cotangentToCLM (I := I)
    (unitEvalSection (I := I) (M := M) g 1 σ b)

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
lemma tensorCovDerivAt_unitEval
    (g : SmoothRiemannianMetric I M) (σ : SmoothCcTensor g 0 1)
    (x : M) (v : TangentSpace I x) :
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 1 I x from
        tensorRSCovariantDerivative I M 0 1 (LeviCivita (I := I) g)
          (fun y : M => σ.toSection y) x v) (unitZeroSec (I := I) (M := M) x) =
      tensor0SCovariantDerivative I M 1 (LeviCivita (I := I) g)
        (fun y : M =>
          (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 1 I y from
            σ.toSection y) (unitZeroSec (I := I) (M := M) y))
        x v := by
  classical
  have happ := tensorRSCovariantDerivative_apply (I := I) (M := M) 0 1
    (LeviCivita (I := I) g) σ.toSection (unitZeroSec (I := I) (M := M)) x v
  refine happ.trans ?_
  refine sub_eq_self.mpr ?_
  refine (congrArg (σ.toSection x) ?_).trans (map_zero _)
  exact tensor0SCovariantDerivative_unitZero_eq_zero (I := I) (M := M)
    (LeviCivita (I := I) g) x v

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
lemma tensor0SCovariantDerivative_one_cotangentToCLM
    (g : SmoothRiemannianMetric I M)
    (α : Π b : M, Tensor0SSpace 1 I b) {x : M}
    (hα : TensorSectionMDiffAt (I := I) 1 α x)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (v : TangentSpace I x) :
    cotangentToCLM (I := I)
        (tensor0SCovariantDerivative I M 1 (LeviCivita (I := I) g) α x v) (Y x) =
      extDerivFun (I := I) (fun b : M => cotangentToCLM (I := I) (α b) (Y b)) x v -
        cotangentToCLM (I := I) (α x) ((LeviCivita (I := I) g).toFun (fun y => Y y) x v) := by
  classical
  have hCLM : ∀ {b : M} (β : Tensor0SSpace 1 I b) (u : TangentSpace I b),
      cotangentToCLM (I := I) β u = Tensor0SSpace.toModel β (fun _ : Fin 1 => u) := by
    intro b β u
    have h := cotangentToDual_apply (I := I) β u
    rw [show cotangentToDual (I := I) β u = cotangentToCLM (I := I) β u from rfl] at h
    rw [h]; rfl
  have hconsEq : ∀ {b : M} (u : TangentSpace I b),
      (Fin.cons u (fun i : Fin 0 => i.elim0) : Fin 1 → TangentSpace I b) =
      (fun _ : Fin 1 => u) := by
    intro b u; funext i; fin_cases i; rfl
  have hpeel := tensor0SCovariantDerivative_succ_consEval_peel (I := I) (M := M)
    g 0 α hα Y v (fun i : Fin 0 => i.elim0)
  rw [hCLM, ← hconsEq (Y x)]
  refine hpeel.trans ?_
  congr 1
  · rw [tensor0SCovariantDerivative_zero_toModel_apply (I := I) (M := M) g
      (fun y : M => curriedSection I M α y (Y y)) x v]
    have hscalar : Tensor0SNabla.scalarFn I M
        (fun y : M => curriedSection I M α y (Y y)) =
        (fun b : M => cotangentToCLM (I := I) (α b) (Y b)) := by
      funext b
      rw [scalarFn_eq_toModel_elim0 (I := I) (M := M)
        (fun y : M => curriedSection I M α y (Y y)) b]
      rw [Tensor0SNabla.curriedSection_apply (I := I) (M := M) α b]
      rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
        (T := α b) (v0 := Y b) (vs := fun i : Fin 0 => i.elim0)]
      rw [hCLM]
      congr 1
      exact hconsEq (Y b)
    rw [hscalar]
    rfl
  · rw [hCLM]
    congr 1
    exact hconsEq ((LeviCivita (I := I) g).toFun (fun y => Y y) x v)

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem cotangentCov_eq_tensorCovDerivAt_ccTensor01
    (g : SmoothRiemannianMetric I M) (σ : SmoothCcTensor g 0 1) {x : M}
    (hθ : MDiffAtCotangent (ccTensorOneForm g σ) x)
    (hUz : TensorSectionMDiffAt (I := I) 1 (unitEvalSection (I := I) (M := M) g 1 σ) x)
    (v w : TangentSpace I x) :
    cotangentCov (LeviCivita (I := I) g) (ccTensorOneForm g σ) x v w =
      cotangentToCLM (I := I)
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 1 I x from
            tensorCovDerivAt g 0 1 σ x v) (unitZeroSec (I := I) (M := M) x)) w := by
  classical
  obtain ⟨X, hXx⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x v
  obtain ⟨Y, hYx⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x w
  have hXmd : MDiffAt (T% (fun b : M => X b)) x :=
    X.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hYmd : MDiffAt (T% (fun b : M => Y b)) x :=
    Y.contMDiff.contMDiffAt.mdifferentiableAt (by simp)

  have hcov : cotangentCov (LeviCivita (I := I) g) (ccTensorOneForm g σ) x v w =
      cotangentScalar ((LeviCivita (I := I) g).toFun) (ccTensorOneForm g σ) x
        (fun b : M => X b) (fun b : M => Y b) := by
    have hco : cotangentCov (LeviCivita (I := I) g) (ccTensorOneForm g σ) x v w =
        cotangentCovAt (LeviCivita (I := I) g) (ccTensorOneForm g σ) x v w := by
      rw [cotangentCov_toFun, cotangentCovFun_apply]
    rw [hco, ← hXx, ← hYx]
    exact cotangentCovAt_apply_of_diff (LeviCivita (I := I) g) hθ hXmd hYmd
  rw [hcov, cotangentScalar_def]
  simp only []
  rw [hXx]

  have hpair := tensor0SCovariantDerivative_one_cotangentToCLM (I := I) (M := M)
    g (unitEvalSection (I := I) (M := M) g 1 σ) hUz Y v

  have hθeq : (fun b : M => ccTensorOneForm g σ b (Y b)) =
      (fun b : M => cotangentToCLM (I := I)
        (unitEvalSection (I := I) (M := M) g 1 σ b) (Y b)) := rfl
  rw [hθeq]
  rw [show (ccTensorOneForm g σ x)
        ((LeviCivita (I := I) g).toFun (fun b : M => Y b) x v) =
      cotangentToCLM (I := I) (unitEvalSection (I := I) (M := M) g 1 σ x)
        ((LeviCivita (I := I) g).toFun (fun y => Y y) x v) from rfl]
  rw [← hpair]

  rw [← hYx]
  congr 2
  rw [tensorCovDerivAt_def]
  exact (tensorCovDerivAt_unitEval (I := I) (M := M) g σ x v).symm

end Connection
end Integral
end DifferentialGeometry
