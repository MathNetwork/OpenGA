import DifferentialGeometry.Geometry.Connection.Chart.NablaComponents.Basic



noncomputable section

namespace DifferentialGeometry
namespace Coordinates

open Bundle Set Tensor0SBundle TensorLieDeriv
open scoped BigOperators Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]

theorem tensor0S_two_eval_coordFrame_sum
    {x₀ : M}
    (Ax : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x₀)
    (Y Z : TangentSpace I x₀) :
    Ax (fun q : Fin 2 => if q = 0 then Y else Z) =
      ∑ i : CoordinateIdx E, ∑ j : CoordinateIdx E,
        (coordinateFrameAt_toBasis (I := I) x₀).coord i Y *
          (coordinateFrameAt_toBasis (I := I) x₀).coord j Z *
          Ax (fun q : Fin 2 =>
            if q = 0 then coordinateFrameAt (I := I) x₀ i x₀
            else coordinateFrameAt (I := I) x₀ j x₀) := by
  classical
  let b := coordinateFrameAt_toBasis (I := I) x₀
  let pair : TangentSpace I x₀ -> TangentSpace I x₀ -> Fin 2 -> TangentSpace I x₀ :=
    fun U V q => if q = 0 then U else V
  have hslot0 (W : TangentSpace I x₀) :
      Ax (pair Y W) =
        ∑ i : CoordinateIdx E, b.coord i Y * Ax (pair (b i) W) := by
    have hupdate (w : TangentSpace I x₀) :
        Function.update (pair Y W) (0 : Fin 2) w = pair w W := by
      funext q
      fin_cases q <;> simp [pair]
    have hmap := Ax.toMultilinearMap.map_update_sum
      (Finset.univ : Finset (CoordinateIdx E)) (0 : Fin 2)
      (fun i : CoordinateIdx E => b.coord i Y • b i) (pair Y W)
    calc
      Ax (pair Y W)
          = Ax (Function.update (pair Y W) (0 : Fin 2)
              (∑ i : CoordinateIdx E, b.coord i Y • b i)) := by
            rw [hupdate]
            congr 1
            funext q
            fin_cases q
            · exact (b.sum_repr Y).symm
            · simp [pair]
      _ = ∑ i : CoordinateIdx E,
            Ax (Function.update (pair Y W) (0 : Fin 2) (b.coord i Y • b i)) := by
            exact hmap
      _ = ∑ i : CoordinateIdx E, b.coord i Y * Ax (pair (b i) W) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [hupdate]
            have hconst :
                pair (b.coord i Y • b i) W =
                  Function.update (pair (b i) W) (0 : Fin 2) (b.coord i Y • b i) := by
              funext q
              fin_cases q <;> simp [pair]
            rw [hconst]
            have hsmul :
                Ax (Function.update (pair (b i) W) (0 : Fin 2) (b.coord i Y • b i)) =
                  b.coord i Y •
                    Ax (Function.update (pair (b i) W) (0 : Fin 2) (b i)) :=
              Ax.toMultilinearMap.map_update_smul (m := pair (b i) W)
                (i := (0 : Fin 2)) (c := b.coord i Y) (x := b i)
            rw [hsmul]
            have hbase :
                Function.update (pair (b i) W) (0 : Fin 2) (b i) = pair (b i) W := by
              funext q
              fin_cases q <;> simp [pair]
            rw [hbase]
            rw [smul_eq_mul]
  have hslot1 (V : TangentSpace I x₀) :
      Ax (pair V Z) =
        ∑ j : CoordinateIdx E, b.coord j Z * Ax (pair V (b j)) := by
    have hupdate (w : TangentSpace I x₀) :
        Function.update (pair V Z) (1 : Fin 2) w = pair V w := by
      funext q
      fin_cases q <;> simp [pair]
    have hmap := Ax.toMultilinearMap.map_update_sum
      (Finset.univ : Finset (CoordinateIdx E)) (1 : Fin 2)
      (fun j : CoordinateIdx E => b.coord j Z • b j) (pair V Z)
    calc
      Ax (pair V Z)
          = Ax (Function.update (pair V Z) (1 : Fin 2)
              (∑ j : CoordinateIdx E, b.coord j Z • b j)) := by
            rw [hupdate]
            congr 1
            funext q
            fin_cases q
            · simp [pair]
            · exact (b.sum_repr Z).symm
      _ = ∑ j : CoordinateIdx E,
            Ax (Function.update (pair V Z) (1 : Fin 2) (b.coord j Z • b j)) := by
            exact hmap
      _ = ∑ j : CoordinateIdx E, b.coord j Z * Ax (pair V (b j)) := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [hupdate]
            have hconst :
                pair V (b.coord j Z • b j) =
                  Function.update (pair V (b j)) (1 : Fin 2) (b.coord j Z • b j) := by
              funext q
              fin_cases q <;> simp [pair]
            rw [hconst]
            have hsmul :
                Ax (Function.update (pair V (b j)) (1 : Fin 2) (b.coord j Z • b j)) =
                  b.coord j Z •
                    Ax (Function.update (pair V (b j)) (1 : Fin 2) (b j)) :=
              Ax.toMultilinearMap.map_update_smul (m := pair V (b j))
                (i := (1 : Fin 2)) (c := b.coord j Z) (x := b j)
            rw [hsmul]
            have hbase :
                Function.update (pair V (b j)) (1 : Fin 2) (b j) = pair V (b j) := by
              funext q
              fin_cases q <;> simp [pair]
            rw [hbase]
            rw [smul_eq_mul]
  calc
    Ax (fun q : Fin 2 => if q = 0 then Y else Z)
        = Ax (pair Y Z) := by
          rfl
    _ = ∑ i : CoordinateIdx E, b.coord i Y * Ax (pair (b i) Z) := by
          exact hslot0 Z
    _ = ∑ i : CoordinateIdx E,
          b.coord i Y * (∑ j : CoordinateIdx E, b.coord j Z * Ax (pair (b i) (b j))) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hslot1 (b i)]
    _ = ∑ i : CoordinateIdx E, ∑ j : CoordinateIdx E,
          b.coord i Y * (b.coord j Z * Ax (pair (b i) (b j))) := by
          simp [Finset.mul_sum]
    _ = ∑ i : CoordinateIdx E, ∑ j : CoordinateIdx E,
          b.coord i Y * b.coord j Z * Ax (pair (b i) (b j)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          refine Finset.sum_congr rfl fun j _ => ?_
          ring
    _ = ∑ i : CoordinateIdx E, ∑ j : CoordinateIdx E,
          (coordinateFrameAt_toBasis (I := I) x₀).coord i Y *
            (coordinateFrameAt_toBasis (I := I) x₀).coord j Z *
            Ax (fun q : Fin 2 =>
              if q = 0 then coordinateFrameAt (I := I) x₀ i x₀
              else coordinateFrameAt (I := I) x₀ j x₀) := by
          simp [b, pair]

theorem nabla0S_two_model_coord
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (⊤ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (⊤ : WithTop ℕ∞)) 2)
    (x₀ : M) (j l : CoordinateIdx E) :
    coordComponent0SAt (I := I)
        (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          2 cov X A x₀)
        (fun q : Fin 2 => if q = 0 then j else l) =
      modelDeriv0SAt (I := I) X x₀ (fun x => A x)
        (fun q : Fin 2 => if q = 0 then j else l) -
        ∑ k : CoordinateIdx E,
          christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
            (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
            x₀ (X x₀) j k *
            coordComponent0SAt (I := I) (A x₀)
              (fun q : Fin 2 => if q = 0 then k else l) -
        ∑ k : CoordinateIdx E,
          christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
            (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
            x₀ (X x₀) l k *
            coordComponent0SAt (I := I) (A x₀)
              (fun q : Fin 2 => if q = 0 then j else k) := by
  classical
  simp only [nabla0SFun, TensorLieDeriv.mcovariantDeriv_tensor0SFromConnection,
    TensorLieDeriv.mcovariantDeriv_tensor0SWithinFromConnection]
  rw [← tensor0SModelAt_coordComponent0SAt (I := I) x₀
    (TensorLieDeriv.mcovariantDeriv_tensor0SWithin
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (⊤ : WithTop ℕ∞)) 2 X
      (connectionEndomorphismInChart (𝕜 := Real) (I := I) cov (fun x => X x) x₀)
      A Set.univ x₀) (fun q : Fin 2 => if q = 0 then j else l)]
  have hmodel := TensorLieDeriv.mcovariantDeriv_tensor0SWithin_two_apply_basis
    (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    (n := (⊤ : WithTop ℕ∞)) (Idx := CoordinateIdx E)
    (basis := Module.finBasis Real E)
    (X := X)
    (ΓX := connectionEndomorphismInChart (𝕜 := Real) (I := I) cov (fun x => X x) x₀)
    (A := A)
    (u := Set.univ)
    (x₀ := x₀)
    (j := j) (l := l)
  have hslots :
      (fun a : Fin 2 => (Module.finBasis Real E) (if a = 0 then j else l)) =
        fun a : Fin 2 => if a = 0 then (Module.finBasis Real E) j
          else (Module.finBasis Real E) l := by
    funext a
    by_cases ha : a = 0 <;> simp [ha]
  refine (congrArg
      (fun f : Fin 2 → E =>
        (TensorLieDeriv.tensor0SModelAt
            (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x₀ x₀
            (TensorLieDeriv.mcovariantDeriv_tensor0SWithin
              (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
              (n := (⊤ : WithTop ℕ∞)) 2 X
              (connectionEndomorphismInChart (𝕜 := Real) (I := I) cov
                (fun x => X x) x₀) A Set.univ x₀)) f)
      hslots).trans (hmodel.trans ?_)
  simp_rw [connCoeff_eq_christoffelAlong_coord (I := I) cov (fun x => X x) x₀]
  simp only [modelDeriv0SAt]
  have hslots_left (k : CoordinateIdx E) :
      (fun a : Fin 2 => (Module.finBasis Real E) (if a = 0 then k else l)) =
        fun a : Fin 2 => if a = 0 then (Module.finBasis Real E) k
          else (Module.finBasis Real E) l := by
    funext a
    by_cases ha : a = 0 <;> simp [ha]
  have hslots_right (k : CoordinateIdx E) :
      (fun a : Fin 2 => (Module.finBasis Real E) (if a = 0 then j else k)) =
        fun a : Fin 2 => if a = 0 then (Module.finBasis Real E) j
          else (Module.finBasis Real E) k := by
    funext a
    by_cases ha : a = 0 <;> simp [ha]
  have hleft_model (k : CoordinateIdx E) :
      (tensor0SModelAt (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 x₀ x₀ (A x₀))
          (fun a : Fin 2 => (Module.finBasis Real E) (if a = 0 then k else l)) =
        coordComponent0SAt (I := I) (A x₀)
          (fun q : Fin 2 => if q = 0 then k else l) := by
    exact tensor0SModelAt_coordComponent0SAt (I := I) x₀ (A x₀)
      (fun q : Fin 2 => if q = 0 then k else l)
  have hright_model (k : CoordinateIdx E) :
      (tensor0SModelAt (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 x₀ x₀ (A x₀))
          (fun a : Fin 2 => (Module.finBasis Real E) (if a = 0 then j else k)) =
        coordComponent0SAt (I := I) (A x₀)
          (fun q : Fin 2 => if q = 0 then j else k) := by
    exact tensor0SModelAt_coordComponent0SAt (I := I) x₀ (A x₀)
      (fun q : Fin 2 => if q = 0 then j else k)
  have hleft_eval (k : CoordinateIdx E) :
      (tensor0SModelAt (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 x₀ x₀ (A x₀))
          (fun a : Fin 2 => (Module.finBasis Real E) (if a = 0 then k else l)) =
        (A x₀) (fun a : Fin 2 =>
          coordinateFrameAt (I := I) x₀ (if a = 0 then k else l) x₀) := by
    rw [hleft_model k]
    simp [coordComponent0SAt, component0S]
  have hright_eval (k : CoordinateIdx E) :
      (tensor0SModelAt (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 x₀ x₀ (A x₀))
          (fun a : Fin 2 => (Module.finBasis Real E) (if a = 0 then j else k)) =
        (A x₀) (fun a : Fin 2 =>
          coordinateFrameAt (I := I) x₀ (if a = 0 then j else k) x₀) := by
    rw [hright_model k]
    simp [coordComponent0SAt, component0S]
  rw [show
      (∑ x : CoordinateIdx E,
        christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
          (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
          x₀ (X x₀) j x *
          (tensor0SModelAt (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            2 x₀ x₀ (A x₀))
            (fun q : Fin 2 =>
              if q = 0 then (Module.finBasis Real E) x else (Module.finBasis Real E) l)) =
        ∑ k : CoordinateIdx E,
          christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
            (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
            x₀ (X x₀) j k *
            coordComponent0SAt (I := I) (A x₀)
              (fun q : Fin 2 => if q = 0 then k else l) from by
        apply Finset.sum_congr rfl
        intro k _
        congr 1
        rw [← hslots_left k]
        exact hleft_model k]
  rw [show
      (∑ x : CoordinateIdx E,
        christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
          (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
          x₀ (X x₀) l x *
          (tensor0SModelAt (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            2 x₀ x₀ (A x₀))
            (fun q : Fin 2 =>
              if q = 0 then (Module.finBasis Real E) j else (Module.finBasis Real E) x)) =
        ∑ k : CoordinateIdx E,
          christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
            (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
            x₀ (X x₀) l k *
            coordComponent0SAt (I := I) (A x₀)
              (fun q : Fin 2 => if q = 0 then j else k) from by
        apply Finset.sum_congr rfl
        intro k _
        congr 1
        rw [← hslots_right k]
        exact hright_model k]
  rw [← hslots]

theorem nabla0S_two_coord
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (⊤ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (⊤ : WithTop ℕ∞)) 2)
    (x₀ : M) (hderiv : ModelDerivEqCoordDeriv0SAt (I := I) X x₀ (fun x => A x))
    (j l : CoordinateIdx E) :
    coordComponent0SAt (I := I)
        (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          2 cov X A x₀)
        (fun q : Fin 2 => if q = 0 then j else l) =
      coordDeriv0SAt (I := I) (fun x => X x) x₀ (fun x => A x)
        (fun q : Fin 2 => if q = 0 then j else l) -
        ∑ k : CoordinateIdx E,
          christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
            (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
            x₀ (X x₀) j k *
            coordComponent0SAt (I := I) (A x₀)
              (fun q : Fin 2 => if q = 0 then k else l) -
        ∑ k : CoordinateIdx E,
          christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
            (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
            x₀ (X x₀) l k *
          coordComponent0SAt (I := I) (A x₀)
              (fun q : Fin 2 => if q = 0 then j else k) := by
  rw [nabla0S_two_model_coord (I := I) cov X A x₀ j l, hderiv]

theorem nabla0SFun_two_eval_coordFrame
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (⊤ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (⊤ : WithTop ℕ∞)) 2)
    (x₀ : M) (hderiv : ModelDerivEqCoordDeriv0SAt (I := I) X x₀ (fun x => A x))
    (j l : CoordinateIdx E) :
    (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      2 cov X A x₀)
        (fun q : Fin 2 =>
          if q = 0 then coordinateFrameAt (I := I) x₀ j x₀
          else coordinateFrameAt (I := I) x₀ l x₀) =
      coordDeriv0SAt (I := I) (fun x => X x) x₀ (fun x => A x)
        (fun q : Fin 2 => if q = 0 then j else l) -
        ∑ k : CoordinateIdx E,
          christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
            (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
            x₀ (X x₀) j k *
            coordComponent0SAt (I := I) (A x₀)
              (fun q : Fin 2 => if q = 0 then k else l) -
        ∑ k : CoordinateIdx E,
          christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
            (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
            x₀ (X x₀) l k *
            coordComponent0SAt (I := I) (A x₀)
              (fun q : Fin 2 => if q = 0 then j else k) := by
  have hslots :
      (fun a : Fin 2 => coordinateFrameAt (I := I) x₀ (if a = 0 then j else l) x₀) =
        fun q : Fin 2 =>
          if q = 0 then coordinateFrameAt (I := I) x₀ j x₀
          else coordinateFrameAt (I := I) x₀ l x₀ := by
    funext q
    by_cases hq : q = 0 <;> simp [hq]
  simpa [coordComponent0SAt, component0S, hslots] using
    nabla0S_two_coord (I := I) cov X A x₀ hderiv j l

theorem nabla0SFun_two_eval_coordFrame_expanded
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (⊤ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (⊤ : WithTop ℕ∞)) 2)
    (x₀ : M) (hderiv : ModelDerivEqCoordDeriv0SAt (I := I) X x₀ (fun x => A x))
    (Y Z : TangentSpace I x₀) :
    (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      2 cov X A x₀) (fun q : Fin 2 => if q = 0 then Y else Z) =
      ∑ j : CoordinateIdx E, ∑ l : CoordinateIdx E,
        (coordinateFrameAt_toBasis (I := I) x₀).coord j Y *
          (coordinateFrameAt_toBasis (I := I) x₀).coord l Z *
          (coordDeriv0SAt (I := I) (fun x => X x) x₀ (fun x => A x)
              (fun q : Fin 2 => if q = 0 then j else l) -
            ∑ k : CoordinateIdx E,
              christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
                (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
                x₀ (X x₀) j k *
                coordComponent0SAt (I := I) (A x₀)
                  (fun q : Fin 2 => if q = 0 then k else l) -
            ∑ k : CoordinateIdx E,
              christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
                (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
                x₀ (X x₀) l k *
                coordComponent0SAt (I := I) (A x₀)
                  (fun q : Fin 2 => if q = 0 then j else k)) := by
  classical
  rw [tensor0S_two_eval_coordFrame_sum (I := I)
    ((nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      2 cov X A x₀)) Y Z]
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [nabla0SFun_two_eval_coordFrame (I := I) cov X A x₀ hderiv j l]

end Coordinates
end DifferentialGeometry
