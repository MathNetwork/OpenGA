import DifferentialGeometry.Geometry.Connection.Laplacian.TensorConnLaplacian
import DifferentialGeometry.Geometry.Connection.ChartTensorNabla.TensorRS.ChartTensorRSSecondCovariantDerivative


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

private noncomputable def smoothOrthoFrameAsSection
    (g : SmoothRiemannianMetric I M) (y : M) (i : Fin (Module.finrank ℝ E)) :
    Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
  ⟨smoothOrthoFrame (I := I) g y i, smoothOrthoFrame_smooth (I := I) g y i⟩

omit [CompleteSpace E] [SigmaCompactSpace M] [BoundarylessManifold I M] in
@[simp]
private lemma smoothOrthoFrameAsSection_toFun
    (g : SmoothRiemannianMetric I M) (y : M)
    (i : Fin (Module.finrank ℝ E)) :
    (smoothOrthoFrameAsSection (I := I) g y i).toFun =
      smoothOrthoFrame (I := I) g y i := rfl

omit [CompleteSpace E] in
theorem rawTensorConnLap_eq_chart
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
    {y : M} (hy : y ∈ chartLeviCivitaGoodSet (I := I) α) :
    rawTensorConnLap (I := I) g r s T.toFun y =
      ∑ i : Fin (Module.finrank ℝ E),
        (chartTensorRSCovariantDerivative (I := I) r s g α
            (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g))
              (smoothOrthoFrame (I := I) g y i) T.toFun)
            (smoothOrthoFrame (I := I) g y i) y -
          (TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g)).toFun T.toFun y
            ((LeviCivita (I := I) g).toFun
              (smoothOrthoFrame (I := I) g y i) y
              (smoothOrthoFrame (I := I) g y i y))) := by
  classical
  letI _h_top : TopologicalSpace
      (TotalSpace (TensorRSModel r s ℝ E)
        (fun x : M => TensorRSSpace r s I x)) :=
    tensorRSBundle_topology r s
  letI _h_fib : FiberBundle (TensorRSModel r s ℝ E)
      (fun x : M => TensorRSSpace r s I x) :=
    tensorRSBundle_fiber r s
  rw [rawTensorConnLap_frame_trace (I := I) g r s T.toFun y]
  refine Finset.sum_congr rfl ?_
  intro i _
  set Bi : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
      smoothOrthoFrameAsSection (I := I) g y i with hBi_def
  have hSecond :=
    chartTensorRSSecondCovariantDerivative_eq_abstract
      (I := I) (M := M) g r s α T Bi Bi (y := y) hy
  have hBi_toFun : Bi.toFun = smoothOrthoFrame (I := I) g y i := by
    rw [hBi_def]
    rfl
  rw [hBi_toFun] at hSecond
  rw [hSecond]

end Connection
end Integral
end DifferentialGeometry

end
