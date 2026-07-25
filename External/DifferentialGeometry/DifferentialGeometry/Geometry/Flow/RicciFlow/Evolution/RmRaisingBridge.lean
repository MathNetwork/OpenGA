import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.NablaRiemannCommutator

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
variable [FiniteDimensional Real E] [InnerProductSpace Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]












omit [InnerProductSpace ℝ E] [I.Boundaryless] [IsManifold I 2 M] in
theorem solution_rm04LowersRm13At
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x : M) :
    DifferentialGeometry.Integral.Connection.Rm04LowersRm13At (I := I)
      (S.base.metric t) x (S.base.rm13 t x) (S.base.rm04 t x) := by
  have h :=
    rm04LowersRm13At_of_realizes
      (I := I) (S.base.metric t)
      (metricCov (I := I) (M := M) (S.base.metric t))
      (metricRm13 (I := I) (M := M) (S.base.metric t))
      (metricRm04 (I := I) (M := M) (S.base.metric t))
      (metricCurvData (I := I) (M := M) (S.base.metric t)).h_rm13
      (metricCurvData (I := I) (M := M) (S.base.metric t)).h_rm04
      x
  simpa [SolutionFamily.rm13, SolutionFamily.rm04] using h
















omit [InnerProductSpace ℝ E] [I.Boundaryless] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem rm13_apply_eq_rm04_raise
    (g : SmoothRiemannianMetric I M) {x : M}
    (Rm13 : Tensor13At (I := I) (M := M) x)
    (Rm04 : Tensor04At (I := I) (M := M) x)
    (hLower : DifferentialGeometry.Integral.Connection.Rm04LowersRm13At (I := I) g x Rm13 Rm04)
    (β : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (X Y Z : TangentSpace I x) :
    Rm13 β (vec3 (I := I) X Y Z) =
      Rm04 (vec4 (I := I) X Y Z (cotangentSharp_gen (I := I) g x β)) := by

  have hL := hLower X Y Z (cotangentSharp_gen (I := I) g x β)

  rw [hL]

  have hβ :
      dualToCotangent_gen (I := I)
          ((tangentFlatLinear_gen (I := I) g x) (cotangentSharp_gen (I := I) g x β)) = β := by

    refine cotangentToDualLinear_injective_gen (I := I) (x := x) ?_
    rw [cotangentToDualLinear_apply_gen, cotangentToDualLinear_apply_gen,
      cotangentToDual_dualToCotangent_gen]

    ext X
    rw [tangentFlatLinear_apply_gen, cotangentToDual_apply_gen,
      cotangentSharp_inner_eval]
  rw [hβ]

















omit [InnerProductSpace ℝ E] [I.Boundaryless] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem curvatureAction0SAt_eq_rm04_raise
    (g : SmoothRiemannianMetric I M)
    (Rm13 : Tensor13Section (I := I) (M := M))
    {x : M} {s : ℕ}
    (Rm04 : Tensor04At (I := I) (M := M) x)
    (hLower : DifferentialGeometry.Integral.Connection.Rm04LowersRm13At (I := I) g x (Rm13 x) Rm04)
    (alpha : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (X Y : TangentSpace I x) (slots : Fin s → TangentSpace I x) :
    curvatureAction0SAt (I := I) Rm13 alpha X Y slots =
      -∑ q : Fin s,
        Rm04 (vec4 (I := I) X Y (slots q)
          (cotangentSharp_gen (I := I) g x
            (oneFormAtSlot0S (I := I) alpha slots q))) := by

  change
    -∑ q : Fin s,
      Rm13 x (oneFormAtSlot0S (I := I) alpha slots q)
        (vec3 (I := I) X Y (slots q)) = _
  congr 1
  refine Finset.sum_congr rfl fun q _ => ?_
  exact rm13_apply_eq_rm04_raise (I := I) g (Rm13 x) Rm04 hLower
    (oneFormAtSlot0S (I := I) alpha slots q) X Y (slots q)























omit [InnerProductSpace ℝ E] [I.Boundaryless] in
theorem nablaLapComm_secondTerm_eq_rm04_raise
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x₀ : M)
    (a b c : CoordinateIdx (𝕜 := Real) E) (m : Fin 4 → CoordinateIdx (𝕜 := Real) E) :
    curvatureAction0SAt (I := I) (S.base.rm13 t)
        (nablaRm04Field (I := I) S t x₀)
        (coordinateFrameAt (I := I) x₀ a x₀) (coordinateFrameAt (I := I) x₀ c x₀)
        (nabla3InnerSlots (I := I) (coordinateFrameAt (I := I) x₀) x₀ b m) =
      -∑ q : Fin 5,
        S.base.rm04 t x₀
          (vec4 (I := I) (coordinateFrameAt (I := I) x₀ a x₀)
            (coordinateFrameAt (I := I) x₀ c x₀)
            (nabla3InnerSlots (I := I) (coordinateFrameAt (I := I) x₀) x₀ b m q)
            (cotangentSharp_gen (I := I) (S.base.metric t) x₀
              (oneFormAtSlot0S (I := I) (nablaRm04Field (I := I) S t x₀)
                (nabla3InnerSlots (I := I) (coordinateFrameAt (I := I) x₀) x₀ b m) q))) :=
  curvatureAction0SAt_eq_rm04_raise (I := I) (S.base.metric t) (S.base.rm13 t)
    (S.base.rm04 t x₀)
    (solution_rm04LowersRm13At (I := I) S t x₀)
    (nablaRm04Field (I := I) S t x₀)
    (coordinateFrameAt (I := I) x₀ a x₀) (coordinateFrameAt (I := I) x₀ c x₀)
    (nabla3InnerSlots (I := I) (coordinateFrameAt (I := I) x₀) x₀ b m)

end DifferentialGeometry.PDE.RicciFlow
