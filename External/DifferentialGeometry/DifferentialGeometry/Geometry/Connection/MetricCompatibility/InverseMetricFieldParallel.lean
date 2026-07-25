import DifferentialGeometry.Geometry.Metric.InverseMetricField
import DifferentialGeometry.Geometry.Connection.TensorNabla.CotangentExtension
import DifferentialGeometry.Geometry.Flow.ConnectionDifference


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold Set Filter FiberBundle
open scoped Manifold Topology ContDiff BigOperators
open Tensor0SBundle

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem inverseMetricSharp_covDeriv_eq (g : SmoothRiemannianMetric I M)
    {X : Π x : M, TangentSpace I x} {x : M}
    (hX : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) y (X y)) x)
    (v : TangentSpace I x) :
    metricSharp (I := I) g x
        ((cotangentCov (LeviCivita (I := I) g)).toFun (metricFlat (I := I) g X) x v) =
      (LeviCivita (I := I) g).toFun X x v := by
  classical
  refine metricFlatLinear_injective (I := I) g x ?_
  ext y
  rw [metricFlatLinear_apply, metricFlatLinear_apply]
  rw [inner_metricSharp (I := I) g x
    ((cotangentCov (LeviCivita (I := I) g)).toFun (metricFlat (I := I) g X) x v) y]
  exact cotangentCov_metricDuality (I := I) g hX v y

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem metricFlat_inverseMetricSharpField_eq (g : SmoothRiemannianMetric I M)
    (β : Π b : M, Tensor0SSpace 1 I b) (b : M) :
    metricFlat (I := I) g (fun y : M => (inverseMetricSharpFib (I := I) g y) (β y)) b =
      cotangentToCLM (I := I) (β b) := by
  refine ContinuousLinearMap.ext (fun w => ?_)
  rw [metricFlat_apply]
  rw [inverseMetricSharpFib_inner (I := I) g b (β b) w]
  rfl

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem inverseMetricSharpField_covGrad_eq_zero (g : SmoothRiemannianMetric I M)
    (β : Π b : M, Tensor0SSpace 1 I b) {x : M}
    (hβ : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) y
        ((inverseMetricSharpFib (I := I) g y) (β y))) x)
    (v : TangentSpace I x) :
    (LeviCivita (I := I) g).toFun
        (fun b : M => (inverseMetricSharpFib (I := I) g b) (β b)) x v =
      inverseMetricSharpFib (I := I) g x
        (dualToCotangent (I := I)
          ((cotangentCov (LeviCivita (I := I) g)).toFun
            (fun b : M => cotangentToCLM (I := I) (β b)) x v)) := by
  classical
  set X : Π b : M, TangentSpace I b :=
    fun b : M => (inverseMetricSharpFib (I := I) g b) (β b) with hX
  have hflat : metricFlat (I := I) g X =
      fun b : M => cotangentToCLM (I := I) (β b) := by
    funext b
    exact metricFlat_inverseMetricSharpField_eq (I := I) g β b
  have hcore := inverseMetricSharp_covDeriv_eq (I := I) g (X := X) hβ v
  rw [hflat] at hcore
  rw [← hcore]
  rw [inverseMetricSharpFib_apply]
  congr 1

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private theorem dualToCotangent_add' {x : M}
    (a b : Module.Dual ℝ (TangentSpace I x)) :
    dualToCotangent (I := I) (a + b) =
      dualToCotangent (I := I) a + dualToCotangent (I := I) b := by
  apply cotangentToDualLinear_injective (I := I) (x := x)
  rw [map_add]
  rw [cotangentToDualLinear_apply, cotangentToDualLinear_apply, cotangentToDualLinear_apply]
  rw [cotangentToDual_dualToCotangent, cotangentToDual_dualToCotangent,
    cotangentToDual_dualToCotangent]

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [SigmaCompactSpace M] [T2Space M] in
theorem cotangentCov_leviCivita_connDiff
    (g₀ g₁ : SmoothRiemannianMetric I M)
    {θ : Π b : M, TangentSpace I b →L[ℝ] ℝ} {x : M}
    (hθ : MDiffAtCotangent (I := I) θ x)
    (v w : TangentSpace I x) :
    ((cotangentCov (LeviCivita (I := I) g₁)).toFun θ x v) w -
        ((cotangentCov (LeviCivita (I := I) g₀)).toFun θ x v) w =
      -θ x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x w v) := by
  classical
  set Y : Π b : M, TangentSpace I b := FiberBundle.extend E w with hYdef
  have hY : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) y (Y y)) x :=
    mdifferentiableAt_extend ..
  have hYx : Y x = w := by rw [hYdef]; simp [FiberBundle.extend]
  have hpair₁ := cotangentCov_dualPairing (LeviCivita (I := I) g₁) hθ hY v
  have hpair₀ := cotangentCov_dualPairing (LeviCivita (I := I) g₀) hθ hY v
  have hsub : ((cotangentCov (LeviCivita (I := I) g₁)).toFun θ x v) (Y x) -
        ((cotangentCov (LeviCivita (I := I) g₀)).toFun θ x v) (Y x) =
      θ x ((LeviCivita (I := I) g₀).toFun Y x v) -
        θ x ((LeviCivita (I := I) g₁).toFun Y x v) := by
    have h := hpair₁.symm.trans hpair₀
    linarith [h]
  have hconn : PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Y x) v =
      (LeviCivita (I := I) g₁).toFun Y x v - (LeviCivita (I := I) g₀).toFun Y x v :=
    PDE.DeTurck.connDiff_apply (I := I) g₁ g₀ (σ := Y) hY v
  rw [hYx] at hsub hconn
  rw [hsub, hconn, map_sub]
  ring

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem covGrad_inverseMetricSharpFib_cross
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (β : Π b : M, Tensor0SSpace 1 I b) {x : M}
    (hβ : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) y
        ((inverseMetricSharpFib (I := I) g₁ y) (β y))) x)
    (hβcot : MDiffAtCotangent (I := I)
      (fun b : M => cotangentToCLM (I := I) (β b)) x)
    (v : TangentSpace I x) :
    (LeviCivita (I := I) g₀).toFun
        (fun b : M => (inverseMetricSharpFib (I := I) g₁ b) (β b)) x v =
      inverseMetricSharpFib (I := I) g₁ x
          (dualToCotangent (I := I)
            ((cotangentCov (LeviCivita (I := I) g₀)).toFun
              (fun b : M => cotangentToCLM (I := I) (β b)) x v))
        - PDE.DeTurck.connDiff (I := I) g₁ g₀ x
            ((inverseMetricSharpFib (I := I) g₁ x) (β x)) v
        + inverseMetricSharpFib (I := I) g₁ x
            (dualToCotangent (I := I)
              (-(cotangentToCLM (I := I) (β x)).comp
                  ((PDE.DeTurck.connDiff (I := I) g₁ g₀ x).flip v)).toLinearMap) := by
  classical
  set X : Π b : M, TangentSpace I b :=
    fun b : M => (inverseMetricSharpFib (I := I) g₁ b) (β b) with hX
  set D : TangentSpace I x →L[ℝ] ℝ :=
    -(cotangentToCLM (I := I) (β x)).comp
        ((PDE.DeTurck.connDiff (I := I) g₁ g₀ x).flip v) with hD
  have hg₀ : (LeviCivita (I := I) g₀).toFun X x v =
      (LeviCivita (I := I) g₁).toFun X x v -
        PDE.DeTurck.connDiff (I := I) g₁ g₀ x (X x) v := by
    have h := PDE.DeTurck.connDiff_apply (I := I) g₁ g₀ (σ := X) hβ v
    rw [h]; abel
  have hpar := inverseMetricSharpField_covGrad_eq_zero (I := I) g₁ β hβ v
  have hbridge :
      ((cotangentCov (LeviCivita (I := I) g₁)).toFun
          (fun b : M => cotangentToCLM (I := I) (β b)) x v).toLinearMap =
        ((cotangentCov (LeviCivita (I := I) g₀)).toFun
            (fun b : M => cotangentToCLM (I := I) (β b)) x v).toLinearMap
          + D.toLinearMap := by
    refine LinearMap.ext (fun w => ?_)
    have hb := cotangentCov_leviCivita_connDiff (I := I) g₀ g₁ hβcot v w
    simp only [hD, LinearMap.add_apply, ContinuousLinearMap.coe_coe,
      ContinuousLinearMap.neg_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply]
    linarith [hb]
  have hsharp_split :
      inverseMetricSharpFib (I := I) g₁ x
          (dualToCotangent (I := I)
            ((cotangentCov (LeviCivita (I := I) g₁)).toFun
              (fun b : M => cotangentToCLM (I := I) (β b)) x v).toLinearMap) =
        inverseMetricSharpFib (I := I) g₁ x
            (dualToCotangent (I := I)
              ((cotangentCov (LeviCivita (I := I) g₀)).toFun
                (fun b : M => cotangentToCLM (I := I) (β b)) x v).toLinearMap)
          + inverseMetricSharpFib (I := I) g₁ x
              (dualToCotangent (I := I) D.toLinearMap) := by
    rw [hbridge, dualToCotangent_add', map_add]
  rw [hg₀, hpar, hsharp_split, hX, hD]
  abel

end Connection
end Integral
end DifferentialGeometry
