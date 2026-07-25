import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.RmRealizationBridge

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false






































































noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Tensor0SBundle
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Integral.Connection
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]












def nabla3InnerSlots
    (frame : CoordinateIdx (𝕜 := Real) E → (x : M) → TangentSpace I x) (x : M)
    (d₂ : CoordinateIdx (𝕜 := Real) E) (m : Fin 4 → CoordinateIdx (𝕜 := Real) E) :
    Fin 5 → TangentSpace I x :=
  Fin.cons (frame d₂ x) (frameTuple (I := I) frame x m)




def nabla3FrameTuple
    (frame : CoordinateIdx (𝕜 := Real) E → (x : M) → TangentSpace I x) (x : M)
    (d₀ d₁ d₂ : CoordinateIdx (𝕜 := Real) E) (m : Fin 4 → CoordinateIdx (𝕜 := Real) E) :
    Fin 7 → TangentSpace I x :=
  metricTraceInput (I := I) (frame d₀ x) (frame d₁ x)
    (nabla3InnerSlots (I := I) frame x d₂ m)

omit [I.Boundaryless] [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
@[simp] theorem nabla3FrameTuple_eq_metricTraceInput
    (frame : CoordinateIdx (𝕜 := Real) E → (x : M) → TangentSpace I x) (x : M)
    (d₀ d₁ d₂ : CoordinateIdx (𝕜 := Real) E) (m : Fin 4 → CoordinateIdx (𝕜 := Real) E) :
    nabla3FrameTuple (I := I) frame x d₀ d₁ d₂ m =
      metricTraceInput (I := I) (frame d₀ x) (frame d₁ x)
        (nabla3InnerSlots (I := I) frame x d₂ m) := rfl

















def nablaLapCommReactionTerm
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x₀ : M)
    (a b c : CoordinateIdx (𝕜 := Real) E) (m : Fin 4 → CoordinateIdx (𝕜 := Real) E) :
    Real :=
  (nabla3Rm04Field (I := I) S t x₀
        (nabla3FrameTuple (I := I) (coordinateFrameAt (I := I) x₀) x₀ a b c m) -
      nabla3Rm04Field (I := I) S t x₀
        (nabla3FrameTuple (I := I) (coordinateFrameAt (I := I) x₀) x₀ a c b m)) +
    curvatureAction0SAt (I := I) (S.base.rm13 t) (nablaRm04Field (I := I) S t x₀)
      (coordinateFrameAt (I := I) x₀ a x₀) (coordinateFrameAt (I := I) x₀ c x₀)
      (nabla3InnerSlots (I := I) (coordinateFrameAt (I := I) x₀) x₀ b m)












omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem nablaLapComm_pointwise
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (x₀ : M)
    (a b c : CoordinateIdx (𝕜 := Real) E) (m : Fin 4 → CoordinateIdx (𝕜 := Real) E) :
    nabla3Rm04Field (I := I) S (t : Real) x₀
        (nabla3FrameTuple (I := I) (coordinateFrameAt (I := I) x₀) x₀ a b c m) -
      nabla3Rm04Field (I := I) S (t : Real) x₀
        (nabla3FrameTuple (I := I) (coordinateFrameAt (I := I) x₀) x₀ c a b m) =
      nablaLapCommReactionTerm (I := I) S (t : Real) x₀ a b c m := by
  classical



  have hR2 :=
    nablaRm04_ricciIdentityAt (I := I) S hS t x₀
      (coordinateFrameAt (I := I) x₀ a x₀) (coordinateFrameAt (I := I) x₀ c x₀)
      (nabla3InnerSlots (I := I) (coordinateFrameAt (I := I) x₀) x₀ b m)



  rw [nablaLapCommReactionTerm]
  simp only [nabla3FrameTuple, nabla3InnerSlots] at hR2 ⊢

  linarith [hR2]

















def roughLapNablaRmComp
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x₀ : M)
    (gInv : CoordinateIdx (𝕜 := Real) E → CoordinateIdx (𝕜 := Real) E → Real)
    (c : CoordinateIdx (𝕜 := Real) E) (m : Fin 4 → CoordinateIdx (𝕜 := Real) E) :
    Real :=
  ∑ a : CoordinateIdx (𝕜 := Real) E, ∑ b : CoordinateIdx (𝕜 := Real) E,
    gInv a b *
      nabla3Rm04Field (I := I) S t x₀
        (nabla3FrameTuple (I := I) (coordinateFrameAt (I := I) x₀) x₀ a b c m)




def nablaRoughLapRmComp
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x₀ : M)
    (gInv : CoordinateIdx (𝕜 := Real) E → CoordinateIdx (𝕜 := Real) E → Real)
    (c : CoordinateIdx (𝕜 := Real) E) (m : Fin 4 → CoordinateIdx (𝕜 := Real) E) :
    Real :=
  ∑ a : CoordinateIdx (𝕜 := Real) E, ∑ b : CoordinateIdx (𝕜 := Real) E,
    gInv a b *
      nabla3Rm04Field (I := I) S t x₀
        (nabla3FrameTuple (I := I) (coordinateFrameAt (I := I) x₀) x₀ c a b m)












omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem nablaLapComm_trace
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (x₀ : M)
    (gInv : CoordinateIdx (𝕜 := Real) E → CoordinateIdx (𝕜 := Real) E → Real)
    (c : CoordinateIdx (𝕜 := Real) E) (m : Fin 4 → CoordinateIdx (𝕜 := Real) E) :
    roughLapNablaRmComp (I := I) S (t : Real) x₀ gInv c m -
        nablaRoughLapRmComp (I := I) S (t : Real) x₀ gInv c m =
      ∑ a : CoordinateIdx (𝕜 := Real) E, ∑ b : CoordinateIdx (𝕜 := Real) E,
        gInv a b * nablaLapCommReactionTerm (I := I) S (t : Real) x₀ a b c m := by
  classical
  rw [roughLapNablaRmComp, nablaRoughLapRmComp]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← mul_sub, nablaLapComm_pointwise (I := I) S hS t x₀ a b c m]
















omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem nablaLapComm_orthonormalTrace
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (x₀ : M)
    (gInv : CoordinateIdx (𝕜 := Real) E → CoordinateIdx (𝕜 := Real) E → Real)
    (horth : ∀ i j : CoordinateIdx (𝕜 := Real) E, gInv i j = if i = j then 1 else 0)
    (c : CoordinateIdx (𝕜 := Real) E) (m : Fin 4 → CoordinateIdx (𝕜 := Real) E) :
    roughLapNablaRmComp (I := I) S (t : Real) x₀ gInv c m -
        nablaRoughLapRmComp (I := I) S (t : Real) x₀ gInv c m =
      ∑ a : CoordinateIdx (𝕜 := Real) E,
        nablaLapCommReactionTerm (I := I) S (t : Real) x₀ a a c m := by
  classical
  rw [nablaLapComm_trace (I := I) S hS t x₀ gInv c m]

  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single a]
  · rw [horth a a, if_pos rfl, one_mul]
  · intro b _ hb
    rw [horth a b, if_neg (fun h => hb h.symm), zero_mul]
  · intro h; exact absurd (Finset.mem_univ a) h






















omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem nablaLapComm_secondTerm_eq
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (x₀ : M)
    (a b c : CoordinateIdx (𝕜 := Real) E) (m : Fin 4 → CoordinateIdx (𝕜 := Real) E) :
    curvatureAction0SAt (I := I) (S.base.rm13 (t : Real))
        (nablaRm04Field (I := I) S (t : Real) x₀)
        (coordinateFrameAt (I := I) x₀ a x₀) (coordinateFrameAt (I := I) x₀ c x₀)
        (nabla3InnerSlots (I := I) (coordinateFrameAt (I := I) x₀) x₀ b m) =
      nabla3Rm04Field (I := I) S (t : Real) x₀
          (nabla3FrameTuple (I := I) (coordinateFrameAt (I := I) x₀) x₀ a c b m) -
        nabla3Rm04Field (I := I) S (t : Real) x₀
          (nabla3FrameTuple (I := I) (coordinateFrameAt (I := I) x₀) x₀ c a b m) := by
  have hR2 :=
    nablaRm04_ricciIdentityAt (I := I) S hS t x₀
      (coordinateFrameAt (I := I) x₀ a x₀) (coordinateFrameAt (I := I) x₀ c x₀)
      (nabla3InnerSlots (I := I) (coordinateFrameAt (I := I) x₀) x₀ b m)
  simp only [nabla3FrameTuple, nabla3InnerSlots] at hR2 ⊢
  exact hR2.symm





omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem nablaLapCommReactionTerm_eq_nabla3
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (x₀ : M)
    (a b c : CoordinateIdx (𝕜 := Real) E) (m : Fin 4 → CoordinateIdx (𝕜 := Real) E) :
    nablaLapCommReactionTerm (I := I) S (t : Real) x₀ a b c m =
      nabla3Rm04Field (I := I) S (t : Real) x₀
          (nabla3FrameTuple (I := I) (coordinateFrameAt (I := I) x₀) x₀ a b c m) -
        nabla3Rm04Field (I := I) S (t : Real) x₀
          (nabla3FrameTuple (I := I) (coordinateFrameAt (I := I) x₀) x₀ c a b m) :=
  (nablaLapComm_pointwise (I := I) S hS t x₀ a b c m).symm












































end DifferentialGeometry.PDE.RicciFlow
