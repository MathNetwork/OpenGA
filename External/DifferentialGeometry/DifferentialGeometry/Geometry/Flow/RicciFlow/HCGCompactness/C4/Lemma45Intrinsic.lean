import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.Lemma45Engine
import DifferentialGeometry.Tensor.RSTensor.Tensor0SRiemannian.Comparison

set_option autoImplicit false
set_option linter.style.longLine false



















noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Tensor0SBundle
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.HCGCompactness
open DifferentialGeometry.Integral.Connection
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]

variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]









omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem compL2_tower_eq_gen
    (g gC : SmoothRiemannianMetric I M) {r : ℕ}
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r)
    (frame : Idx → (x : M) → TangentSpace I x) {u : Set M}
    (hframe : IsLocalFrameOn I E (1 : WithTop ℕ∞) frame u) (hu : IsOpen u)
    {y : M} (hy : y ∈ u)
    (hinv : Tensor0SBundle.MetricInverseInBasis (I := I) g y (hframe.toBasisAt hy)
      (Tensor0SBundle.identityInvMetric (Idx := Idx)))
    (j : ℕ) :
    compL2 (iterCovComp (I := I) frame
        (fun y' => christoffelSymbolInFrame
          (leviCivitaConnectionOfMetric (I := I) gC) frame hframe y')
        (frameComp0S (I := I) T frame) j y) =
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g y (r + j)
        (iterCov (I := I) gC r T j y)) := by
  rw [compL2]
  congr 1
  rw [Tensor0SBundle.normSq0S_identity_eq_sum_sq (I := I) g y (r + j)
    (hframe.toBasisAt hy) hinv (iterCov (I := I) gC r T j y)]
  simp only [compL2Sq]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [iterCovComp_eq_iterCov (I := I) gC T frame hframe hu j hy n]
  congr 1
  rw [Tensor0SBundle.component0S_apply]
  congr 1
  funext q
  rw [IsLocalFrameOn.toBasisAt_coe]
  rfl








omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem hF3_term {q₂ : ℕ} {u : Set M} (hu : IsOpen u)
    (g gRef : SmoothRiemannianMetric I M)
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) q₂)
    (frame : Idx → (x : M) → TangentSpace I x)
    (hframe : IsLocalFrameOn I E (1 : WithTop ℕ∞) frame u)
    {x : M} (hx : x ∈ u)
    (hinv : Tensor0SBundle.MetricInverseInBasis (I := I) g x (hframe.toBasisAt hx)
      (Tensor0SBundle.identityInvMetric (Idx := Idx)))
    (eps Cc : Real) (r : ℕ)
    (hineq :
      compL2 (iterCovComp (I := I) frame
          (fun y' => christoffelSymbolInFrame
            (leviCivitaConnectionOfMetric (I := I) g) frame hframe y')
          (frameComp0S (I := I) T frame) r x) ≤
        compL2 (iterCovComp (I := I) frame
          (fun y' => christoffelSymbolInFrame
            (leviCivitaConnectionOfMetric (I := I) gRef) frame hframe y')
          (frameComp0S (I := I) T frame) r x) +
        eps * Cc * ∑ k ∈ Finset.range r,
          compL2 (iterCovComp (I := I) frame
            (fun y' => christoffelSymbolInFrame
              (leviCivitaConnectionOfMetric (I := I) gRef) frame hframe y')
            (frameComp0S (I := I) T frame) k x)) :
    Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x (q₂ + r) (iterCov (I := I) g q₂ T r x)) ≤
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x (q₂ + r)
        (iterCov (I := I) gRef q₂ T r x)) +
      eps * Cc * ∑ k ∈ Finset.range r,
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x (q₂ + k)
          (iterCov (I := I) gRef q₂ T k x)) := by
  rw [← compL2_tower_eq_gen (I := I) g g T frame hframe hu hx hinv r,
    ← compL2_tower_eq_gen (I := I) g gRef T frame hframe hu hx hinv r,
    show (∑ k ∈ Finset.range r,
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x (q₂ + k)
          (iterCov (I := I) gRef q₂ T k x))) =
      ∑ k ∈ Finset.range r,
        compL2 (iterCovComp (I := I) frame
          (fun y' => christoffelSymbolInFrame
            (leviCivitaConnectionOfMetric (I := I) gRef) frame hframe y')
          (frameComp0S (I := I) T frame) k x) from
      Finset.sum_congr rfl fun k _ =>
        (compL2_tower_eq_gen (I := I) g gRef T frame hframe hu hx hinv k).symm]
  exact hineq

end DifferentialGeometry.PDE.RicciFlow
