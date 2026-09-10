import Definitions.Def_OpenGA_ImmersedMetric
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Bundle
import Mathlib.Data.Matrix.Mul
import Mathlib.Geometry.Manifold.Algebra.Monoid
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.VectorBundle.Riemannian
import Verified.ClosedSurface_DifferentialGeometry_Bundle_TangentSpace
import Verified.ClosedSurface_DifferentialGeometry_Geometry_Metric_ChartGram
import Verified.ClosedSurface_DifferentialGeometry_Geometry_Metric_TensorInner_MetricFiberData
import Verified.ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Basis
import Verified.ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Bundle
import Verified.ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Comp
import Verified.ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Fiber
import Verified.ClosedSurface_DifferentialGeometry_Tensor_RSTensor_Defs

namespace DifferentialGeometry

namespace Tensor0SBundle

noncomputable section

open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def cotangentToCLM {x : M} (α : Tensor0SSpace 1 I x) :
    TangentSpace I x →L[Real] Real where
  toFun X := α (fun _ => X)
  map_add' X Y := by
    have h := α.toMultilinearMap.map_update_add (fun _ => 0) 0 X Y
    change α.toMultilinearMap (fun _ => X + Y) =
      α.toMultilinearMap (fun _ => X) + α.toMultilinearMap (fun _ => Y)
    rw [show (fun _ : Fin 1 => X + Y) = Function.update (fun _ => 0) 0 (X + Y) by
      funext i; fin_cases i; simp]
    rw [show (fun _ : Fin 1 => X) = Function.update (fun _ => 0) 0 X by
      funext i; fin_cases i; simp]
    rw [show (fun _ : Fin 1 => Y) = Function.update (fun _ => 0) 0 Y by
      funext i; fin_cases i; simp]
    exact h
  map_smul' c X := by
    have h := α.toMultilinearMap.map_update_smul (fun _ => 0) 0 c X
    change α.toMultilinearMap (fun _ => c • X) = c • α.toMultilinearMap (fun _ => X)
    rw [show (fun _ : Fin 1 => c • X) = Function.update (fun _ => 0) 0 (c • X) by
      funext i; fin_cases i; simp]
    rw [show (fun _ : Fin 1 => X) = Function.update (fun _ => 0) 0 X by
      funext i; fin_cases i; simp]
    exact h
  cont := α.cont.comp (continuous_pi fun _ => continuous_id)

def cotangentToDual {x : M} (α : Tensor0SSpace 1 I x) :
    Module.Dual Real (TangentSpace I x) :=
  (cotangentToCLM (I := I) α).toLinearMap

omit [FiniteDimensional ℝ E] in
@[simp] theorem cotangentToDual_apply {x : M}
    (α : Tensor0SSpace 1 I x) (X : TangentSpace I x) :
    cotangentToDual (I := I) α X = α (fun _ : Fin 1 => X) := by
  rfl

def cotangentToDualLinear {x : M} :
    Tensor0SSpace 1 I x →ₗ[Real] Module.Dual Real (TangentSpace I x) where
  toFun := cotangentToDual (I := I)
  map_add' α β := by
    ext X
    rfl
  map_smul' c α := by
    ext X
    rfl

omit [FiniteDimensional ℝ E] in
theorem cotangentToDualLinear_injective {x : M} :
    Function.Injective (cotangentToDualLinear (I := I) (x := x)) := by
  intro α β h
  ext v
  have hv :
      (fun _ : Fin 1 => v 0) = v := by
    funext i
    fin_cases i
    rfl
  have h0 := congrArg (fun L : Module.Dual Real (TangentSpace I x) => L (v 0)) h
  simpa [cotangentToDualLinear, cotangentToDual_apply, hv] using h0

def cotangentSharpLinear (g : SmoothMetric I M) (x : M) :
    Tensor0SSpace 1 I x →ₗ[Real] TangentSpace I x :=
  ((tangentMetricData (I := I) g x).metric.sharp).toLinearMap.comp
    (cotangentToDualLinear (I := I) (x := x))

def cotangentSharp (g : SmoothMetric I M) (x : M)
    (α : Tensor0SSpace 1 I x) : TangentSpace I x :=
  cotangentSharpLinear (I := I) g x α

@[simp] theorem cotangentSharpLinear_apply
    (g : SmoothMetric I M) (x : M) (α : Tensor0SSpace 1 I x) :
    cotangentSharpLinear (I := I) g x α = cotangentSharp (I := I) g x α := by
  rfl

theorem cotangentSharpLinear_injective
    (g : SmoothMetric I M) (x : M) :
    Function.Injective (cotangentSharpLinear (I := I) g x) := by
  intro α β h
  apply cotangentToDualLinear_injective (I := I) (x := x)
  exact ((tangentMetricData (I := I) g x).metric.sharp.injective h)

def cotangentInner (g : SmoothMetric I M) (x : M)
    (α β : Tensor0SSpace 1 I x) : Real :=
  g.inner x
    (cotangentSharpLinear (I := I) g x α)
    (cotangentSharpLinear (I := I) g x β)

def cotangentFlatLinear (g : SmoothMetric I M) (x : M) :
    Tensor0SSpace 1 I x →ₗ[Real] Module.Dual Real (Tensor0SSpace 1 I x) where
  toFun α :=
    { toFun := fun β => cotangentInner (I := I) g x α β
      map_add' := by
        intro β γ
        let S := cotangentSharpLinear (I := I) g x
        have hS : S (β + γ) = S β + S γ := map_add S β γ
        change g.inner x (S α) (S (β + γ)) =
          g.inner x (S α) (S β) + g.inner x (S α) (S γ)
        rw [hS]
        simp
      map_smul' := by
        intro c β
        let S := cotangentSharpLinear (I := I) g x
        have hS : S (c • β) = c • S β := map_smul S c β
        change g.inner x (S α) (S (c • β)) = c * g.inner x (S α) (S β)
        rw [hS]
        simp }
  map_add' α β := by
    ext γ
    let S := cotangentSharpLinear (I := I) g x
    have hS : S (α + β) = S α + S β := map_add S α β
    change g.inner x (S (α + β)) (S γ) =
      g.inner x (S α) (S γ) + g.inner x (S β) (S γ)
    rw [hS]
    simp
  map_smul' c α := by
    ext β
    let S := cotangentSharpLinear (I := I) g x
    have hS : S (c • α) = c • S α := map_smul S c α
    change g.inner x (S (c • α)) (S β) = c * g.inner x (S α) (S β)
    rw [hS]
    simp

theorem cotangentFlatLinear_injective
    (g : SmoothMetric I M) (x : M) :
    Function.Injective (cotangentFlatLinear (I := I) g x) := by
  intro α β h
  have hsub : cotangentSharpLinear (I := I) g x (α - β) = 0 := by
    by_contra hsharp
    have hpos :
        0 <
          g.inner x
            (cotangentSharpLinear (I := I) g x (α - β))
            (cotangentSharpLinear (I := I) g x (α - β)) :=
      g.pos x (cotangentSharpLinear (I := I) g x (α - β)) hsharp
    have h_eval :
        cotangentFlatLinear (I := I) g x α (α - β) =
          cotangentFlatLinear (I := I) g x β (α - β) :=
      congrArg
        (fun L : Module.Dual Real (Tensor0SSpace 1 I x) => L (α - β)) h
    have hdiff : cotangentFlatLinear (I := I) g x (α - β) (α - β) = 0 := by
      calc
        cotangentFlatLinear (I := I) g x (α - β) (α - β)
            = (cotangentFlatLinear (I := I) g x α -
                cotangentFlatLinear (I := I) g x β) (α - β) := by
                exact congrArg
                  (fun L : Module.Dual Real (Tensor0SSpace 1 I x) => L (α - β))
                  (map_sub (cotangentFlatLinear (I := I) g x) α β)
        _ = cotangentFlatLinear (I := I) g x α (α - β) -
              cotangentFlatLinear (I := I) g x β (α - β) := rfl
        _ = 0 := sub_eq_zero.mpr h_eval
    have hzero :
        g.inner x
            (cotangentSharpLinear (I := I) g x (α - β))
            (cotangentSharpLinear (I := I) g x (α - β)) = 0 := by
      simpa [cotangentFlatLinear, cotangentInner] using hdiff
    exact (lt_irrefl (0 : Real)) (hzero ▸ hpos)
  apply cotangentSharpLinear_injective (I := I) g x
  have hdiff :
      cotangentSharpLinear (I := I) g x α -
        cotangentSharpLinear (I := I) g x β = 0 := by
    have hmap :
        cotangentSharpLinear (I := I) g x (α - β) =
          cotangentSharpLinear (I := I) g x α -
            cotangentSharpLinear (I := I) g x β :=
      map_sub (cotangentSharpLinear (I := I) g x) α β
    rwa [hmap] at hsub
  exact sub_eq_zero.mp hdiff

def cotangentMetricData (g : SmoothMetric I M) (x : M) :
    MetricFiberData (Tensor0SSpace 1 I x) :=
  MetricFiberData.ofFlat
    (cotangentFlatLinear (I := I) g x)
    (cotangentFlatLinear_injective (I := I) g x)
    (by
      intro α β
      change g.inner x
          (cotangentSharpLinear (I := I) g x α)
          (cotangentSharpLinear (I := I) g x β) =
        g.inner x
          (cotangentSharpLinear (I := I) g x β)
          (cotangentSharpLinear (I := I) g x α)
      exact g.symm x _ _)
    (by
      intro α
      by_cases hα : cotangentSharpLinear (I := I) g x α = 0
      · change 0 <=
          g.inner x
            (cotangentSharpLinear (I := I) g x α)
            (cotangentSharpLinear (I := I) g x α)
        rw [hα]
        simp
      · exact le_of_lt (g.pos x (cotangentSharpLinear (I := I) g x α) hα))

end

end Tensor0SBundle

end DifferentialGeometry
