import DifferentialGeometry.Geometry.Connection.ChartTensorNabla.TensorRS.ChartTensorRSCovariantDerivativeAgreement
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Defs

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff BigOperators
open Tensor0SBundle

namespace DifferentialGeometry
namespace Integral
namespace Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma covApply_covRS_contMDiff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {T : Π b : M, TensorRSSpace r s I b}
    (hT_total : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T y)))
    {X : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X)) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y
        (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
            (LeviCivita (I := I) g)) X T y)) := by
  classical
  have hT_plus : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
      ((∞ : WithTop ℕ∞) + 1)
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T y)) := by
    rw [show ((∞ : WithTop ℕ∞) + 1) = ∞ from rfl]
    exact hT_total
  have hOn :
      ContMDiffOn I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
        (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
          (E := fun z : M => TensorRSSpace r s I z) y
          (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g)) X T y)) Set.univ :=
    covApply_contMDiffOn
      (cov := TensorRSNabla.tensorRSCovariantDerivative I M r s
        (LeviCivita (I := I) g)) hX hT_plus
  intro b
  exact hOn.contMDiffAt (Filter.univ_mem)

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem chartTensorRSSecondCovariantDerivative_eq_abstract
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T :
      letI _h_top : TopologicalSpace
          (TotalSpace (TensorRSModel r s ℝ E)
            (fun x : M => TensorRSSpace r s I x)) :=
        tensorRSBundle_topology r s
      letI _h_fib : FiberBundle (TensorRSModel r s ℝ E)
          (fun x : M => TensorRSSpace r s I x) :=
        tensorRSBundle_fiber r s
      Cₛ^∞⟮I; TensorRSModel r s ℝ E,
        fun b => TensorRSSpace r s I b⟯)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (X' : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {y : M} (hy : y ∈ chartLeviCivitaGoodSet (I := I) α) :
    (TensorRSNabla.tensorRSCovariantDerivative I M r s
        (LeviCivita (I := I) g)).toFun
      (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
        (LeviCivita (I := I) g)) X.toFun T.toFun) y (X'.toFun y) =
      chartTensorRSCovariantDerivative (I := I) r s g α
        (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
          (LeviCivita (I := I) g)) X.toFun T.toFun) X'.toFun y := by
  classical
  letI _h_top : TopologicalSpace
      (TotalSpace (TensorRSModel r s ℝ E)
        (fun x : M => TensorRSSpace r s I x)) :=
    tensorRSBundle_topology r s
  letI _h_fib : FiberBundle (TensorRSModel r s ℝ E)
      (fun x : M => TensorRSSpace r s I x) :=
    tensorRSBundle_fiber r s
  have hCovApply_smooth :
      ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
        (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
          (E := fun z : M => TensorRSSpace r s I z) y
          (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g)) X.toFun T.toFun y)) :=
    covApply_covRS_contMDiff (I := I) g r s T.contMDiff X.contMDiff
  set S : Cₛ^∞⟮I; TensorRSModel r s ℝ E,
      fun b : M => TensorRSSpace r s I b⟯ :=
    { toFun := covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
        (LeviCivita (I := I) g)) X.toFun T.toFun
      contMDiff_toFun := hCovApply_smooth } with hS_def
  have hFirst :=
    chartTensorRSCovariantDerivative_eq_abstract_on_chartLeviCivitaGoodSet (I := I) (M := M)
      g r s α S X' (b := y) hy
  have hS_toFun : S.toFun =
      covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
        (LeviCivita (I := I) g)) X.toFun T.toFun := by
    rw [hS_def]
  rw [hS_toFun] at hFirst
  exact hFirst.symm

end Connection
end Integral
end DifferentialGeometry

end
