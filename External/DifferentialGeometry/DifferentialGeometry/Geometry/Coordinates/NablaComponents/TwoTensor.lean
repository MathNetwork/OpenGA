import DifferentialGeometry.Geometry.Coordinates.NablaComponents.Basic








set_option autoImplicit false
set_option linter.style.longLine false

noncomputable section

namespace DifferentialGeometry.Tensor.Coordinates

open Bundle Set Tensor0SBundle TensorLieDeriv
open scoped BigOperators Manifold ContDiff Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I 1 M] [IsManifold I 2 M] [h_mfd : IsManifold I ∞ M]



omit [CompleteSpace 𝕜] [IsManifold I 2 M] in
theorem tensor0S_two_eval_coordFrame_sum
    {x₀ : M}
    (Ax : Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) 2 x₀)
    (Y Z : TangentSpace I x₀) :
    Ax (fun q : Fin 2 => if q = 0 then Y else Z) =
      ∑ i : CoordinateIdx (𝕜 := 𝕜) E, ∑ j : CoordinateIdx (𝕜 := 𝕜) E,
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
        ∑ i : CoordinateIdx (𝕜 := 𝕜) E, b.coord i Y * Ax (pair (b i) W) := by
    have hupdate (w : TangentSpace I x₀) :
        Function.update (pair Y W) (0 : Fin 2) w = pair w W := by
      funext q
      fin_cases q <;> simp [pair]
    have hmap := Ax.toMultilinearMap.map_update_sum
      (Finset.univ : Finset (CoordinateIdx (𝕜 := 𝕜) E)) (0 : Fin 2)
      (fun i : CoordinateIdx (𝕜 := 𝕜) E => b.coord i Y • b i) (pair Y W)
    calc
      Ax (pair Y W)
          = Ax (Function.update (pair Y W) (0 : Fin 2)
              (∑ i : CoordinateIdx (𝕜 := 𝕜) E, b.coord i Y • b i)) := by
            rw [hupdate]
            congr 1
            funext q
            fin_cases q
            · exact (b.sum_repr Y).symm
            · simp [pair]
      _ = ∑ i : CoordinateIdx (𝕜 := 𝕜) E,
            b.coord i Y *
              Ax (Function.update (pair Y W) (0 : Fin 2) (b i)) := by
            simpa using hmap
      _ = ∑ i : CoordinateIdx (𝕜 := 𝕜) E, b.coord i Y * Ax (pair (b i) W) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [hupdate]
  have hslot1 (V : TangentSpace I x₀) :
      Ax (pair V Z) =
        ∑ j : CoordinateIdx (𝕜 := 𝕜) E, b.coord j Z * Ax (pair V (b j)) := by
    have hupdate (w : TangentSpace I x₀) :
        Function.update (pair V Z) (1 : Fin 2) w = pair V w := by
      funext q
      fin_cases q <;> simp [pair]
    have hmap := Ax.toMultilinearMap.map_update_sum
      (Finset.univ : Finset (CoordinateIdx (𝕜 := 𝕜) E)) (1 : Fin 2)
      (fun j : CoordinateIdx (𝕜 := 𝕜) E => b.coord j Z • b j) (pair V Z)
    calc
      Ax (pair V Z)
          = Ax (Function.update (pair V Z) (1 : Fin 2)
              (∑ j : CoordinateIdx (𝕜 := 𝕜) E, b.coord j Z • b j)) := by
            rw [hupdate]
            congr 1
            funext q
            fin_cases q
            · simp [pair]
            · exact (b.sum_repr Z).symm
      _ = ∑ j : CoordinateIdx (𝕜 := 𝕜) E,
            b.coord j Z *
              Ax (Function.update (pair V Z) (1 : Fin 2) (b j)) := by
            simpa using hmap
      _ = ∑ j : CoordinateIdx (𝕜 := 𝕜) E, b.coord j Z * Ax (pair V (b j)) := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [hupdate]
  calc
    Ax (fun q : Fin 2 => if q = 0 then Y else Z)
        = Ax (pair Y Z) := by
          rfl
    _ = ∑ i : CoordinateIdx (𝕜 := 𝕜) E, b.coord i Y * Ax (pair (b i) Z) := by
          exact hslot0 Z
    _ = ∑ i : CoordinateIdx (𝕜 := 𝕜) E,
          b.coord i Y * (∑ j : CoordinateIdx (𝕜 := 𝕜) E, b.coord j Z * Ax (pair (b i) (b j))) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hslot1 (b i)]
    _ = ∑ i : CoordinateIdx (𝕜 := 𝕜) E, ∑ j : CoordinateIdx (𝕜 := 𝕜) E,
          b.coord i Y * (b.coord j Z * Ax (pair (b i) (b j))) := by
          simp [Finset.mul_sum]
    _ = ∑ i : CoordinateIdx (𝕜 := 𝕜) E, ∑ j : CoordinateIdx (𝕜 := 𝕜) E,
          b.coord i Y * b.coord j Z * Ax (pair (b i) (b j)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          refine Finset.sum_congr rfl fun j _ => ?_
          ring
    _ = ∑ i : CoordinateIdx (𝕜 := 𝕜) E, ∑ j : CoordinateIdx (𝕜 := 𝕜) E,
          (coordinateFrameAt_toBasis (I := I) x₀).coord i Y *
            (coordinateFrameAt_toBasis (I := I) x₀).coord j Z *
            Ax (fun q : Fin 2 =>
              if q = 0 then coordinateFrameAt (I := I) x₀ i x₀
              else coordinateFrameAt (I := I) x₀ j x₀) := by
          simp [b, pair]



omit [IsManifold I 2 M] in
omit h_mfd in
theorem tensor0S_two_symm_of_coordFrame [IsManifold I ∞ M]
    {Idx : Type*} [Finite Idx]
    {x₀ : M}
    (basis : Module.Basis Idx 𝕜 (TangentSpace I x₀))
    (A : Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) 2 x₀)
    (hcoord : ∀ i j : Idx,
      A (fun q : Fin 2 => if q = 0 then basis i else basis j) =
        A (fun q : Fin 2 => if q = 0 then basis j else basis i)) :
    ∀ Y Z : TangentSpace I x₀,
      A (fun q : Fin 2 => if q = 0 then Y else Z) =
        A (fun q : Fin 2 => if q = 0 then Z else Y) := by
  classical
  letI : Fintype Idx := Fintype.ofFinite Idx
  let swapped :
      Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) 2 x₀ :=
    A.domDomCongr (Equiv.swap (0 : Fin 2) 1)
  have htensor : A = swapped := by
    apply ext0S_basis (I := I) basis
    intro slots
    have h := hcoord (slots 0) (slots 1)
    have hslots :
        (fun a => basis (slots a)) =
          fun q : Fin 2 => if q = 0 then basis (slots 0) else basis (slots 1) := by
      funext q
      fin_cases q <;> simp
    have hswap :
        (fun a : Fin 2 =>
            (fun q : Fin 2 => if q = 0 then basis (slots 0) else basis (slots 1))
              ((Equiv.swap (0 : Fin 2) 1) a)) =
          (fun q : Fin 2 => if q = 0 then basis (slots 1) else basis (slots 0)) := by
      funext q
      fin_cases q <;> simp
    change
      A (fun a => basis (slots a)) =
        A (fun a : Fin 2 =>
          (fun b => basis (slots b)) ((Equiv.swap (0 : Fin 2) 1) a))
    rw [hslots, hswap]
    exact h
  intro Y Z
  have h_eval := congrArg
    (fun B :
      Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) 2 x₀ =>
        B (fun q : Fin 2 => if q = 0 then Y else Z)) htensor
  have hswapYZ :
      (fun i : Fin 2 =>
          if (Equiv.swap (0 : Fin 2) 1 i) = 0 then Y else Z) =
        fun q : Fin 2 => if q = 0 then Z else Y := by
    funext q
    fin_cases q <;> simp
  change A (fun q : Fin 2 => if q = 0 then Y else Z) =
    (ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1) A)
      (fun q : Fin 2 => if q = 0 then Y else Z) at h_eval
  rw [ContinuousMultilinearMap.domDomCongr_apply, hswapYZ] at h_eval
  exact h_eval

section TopRegularity




omit h_mfd in
theorem nabla0S_two_model_coord [IsManifold I ∞ M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (A : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2)
    (x₀ : M) (j l : CoordinateIdx (𝕜 := 𝕜) E) :
    coordComponent0SAt (I := I)
        (nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
          2 cov X A x₀)
        (fun q : Fin 2 => if q = 0 then j else l) =
      modelDeriv0SAt (I := I) X x₀ (fun x => A x)
        (fun q : Fin 2 => if q = 0 then j else l) -
        ∑ k : CoordinateIdx (𝕜 := 𝕜) E,
          christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
            (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
            x₀ (X x₀) j k *
            coordComponent0SAt (I := I) (A x₀)
              (fun q : Fin 2 => if q = 0 then k else l) -
        ∑ k : CoordinateIdx (𝕜 := 𝕜) E,
          christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
            (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
            x₀ (X x₀) l k *
            coordComponent0SAt (I := I) (A x₀)
              (fun q : Fin 2 => if q = 0 then j else k) := by
  classical
  let slots : Fin 2 -> CoordinateIdx (𝕜 := 𝕜) E := fun q => if q = 0 then j else l
  have h := nabla0S_model_coordFrame_slots
    (I := I) cov X A x₀ slots
  have hupdate0 (k : CoordinateIdx (𝕜 := 𝕜) E) :
      Function.update slots 0 k = (fun q : Fin 2 => if q = 0 then k else l) := by
    funext q
    fin_cases q <;> simp [slots]
  have hupdate1 (k : CoordinateIdx (𝕜 := 𝕜) E) :
      Function.update slots 1 k = (fun q : Fin 2 => if q = 0 then j else k) := by
    funext q
    fin_cases q <;> simp [slots]
  rw [h]
  simp [slots, Fin.sum_univ_two, hupdate0, hupdate1]
  ring_nf



omit h_mfd in
theorem nabla0S_two_coord [IsManifold I ∞ M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (A : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2)
    (x₀ : M) (hderiv : ModelDerivEqCoordDeriv0SAt (I := I) X x₀ (fun x => A x))
    (j l : CoordinateIdx (𝕜 := 𝕜) E) :
    coordComponent0SAt (I := I)
        (nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
          2 cov X A x₀)
        (fun q : Fin 2 => if q = 0 then j else l) =
      coordDeriv0SAt (I := I) (fun x => X x) x₀ (fun x => A x)
        (fun q : Fin 2 => if q = 0 then j else l) -
        ∑ k : CoordinateIdx (𝕜 := 𝕜) E,
          christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
            (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
            x₀ (X x₀) j k *
            coordComponent0SAt (I := I) (A x₀)
              (fun q : Fin 2 => if q = 0 then k else l) -
        ∑ k : CoordinateIdx (𝕜 := 𝕜) E,
          christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
            (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
            x₀ (X x₀) l k *
          coordComponent0SAt (I := I) (A x₀)
              (fun q : Fin 2 => if q = 0 then j else k) := by
  classical
  let slots : Fin 2 -> CoordinateIdx (𝕜 := 𝕜) E := fun q => if q = 0 then j else l
  have h := nabla0S_coordFrame_slots
    (I := I) cov X A x₀ hderiv slots
  have hupdate0 (k : CoordinateIdx (𝕜 := 𝕜) E) :
      Function.update slots 0 k = (fun q : Fin 2 => if q = 0 then k else l) := by
    funext q
    fin_cases q <;> simp [slots]
  have hupdate1 (k : CoordinateIdx (𝕜 := 𝕜) E) :
      Function.update slots 1 k = (fun q : Fin 2 => if q = 0 then j else k) := by
    funext q
    fin_cases q <;> simp [slots]
  rw [h]
  simp [slots, Fin.sum_univ_two, hupdate0, hupdate1]
  ring_nf





omit h_mfd in
theorem nabla0SFun_two_eval_coordFrame [IsManifold I ∞ M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (A : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2)
    (x₀ : M) (hderiv : ModelDerivEqCoordDeriv0SAt (I := I) X x₀ (fun x => A x))
    (j l : CoordinateIdx (𝕜 := 𝕜) E) :
    (nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      2 cov X A x₀)
        (fun q : Fin 2 =>
          if q = 0 then coordinateFrameAt (I := I) x₀ j x₀
          else coordinateFrameAt (I := I) x₀ l x₀) =
      coordDeriv0SAt (I := I) (fun x => X x) x₀ (fun x => A x)
        (fun q : Fin 2 => if q = 0 then j else l) -
        ∑ k : CoordinateIdx (𝕜 := 𝕜) E,
          christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
            (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
            x₀ (X x₀) j k *
            coordComponent0SAt (I := I) (A x₀)
              (fun q : Fin 2 => if q = 0 then k else l) -
        ∑ k : CoordinateIdx (𝕜 := 𝕜) E,
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



omit h_mfd in
theorem nabla0SFun_two_eval_coordFrame_symm_of_symm [IsManifold I ∞ M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (A : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2)
    (x₀ : M) (hderiv : ModelDerivEqCoordDeriv0SAt (I := I) X x₀ (fun x => A x))
    (hsymm : ∀ y : M, ∀ U V : TangentSpace I y,
      A y (fun q : Fin 2 => if q = 0 then U else V) =
        A y (fun q : Fin 2 => if q = 0 then V else U))
    (j l : CoordinateIdx (𝕜 := 𝕜) E) :
    (nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      2 cov X A x₀)
        (fun q : Fin 2 =>
          if q = 0 then coordinateFrameAt (I := I) x₀ j x₀
          else coordinateFrameAt (I := I) x₀ l x₀) =
      (nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        2 cov X A x₀)
          (fun q : Fin 2 =>
            if q = 0 then coordinateFrameAt (I := I) x₀ l x₀
            else coordinateFrameAt (I := I) x₀ j x₀) := by
  classical
  have hleft := nabla0SFun_two_eval_coordFrame (I := I) cov X A x₀ hderiv j l
  have hright := nabla0SFun_two_eval_coordFrame (I := I) cov X A x₀ hderiv l j
  have hD :
      coordDeriv0SAt (I := I) (fun x => X x) x₀ (fun x => A x)
          (fun q : Fin 2 => if q = 0 then j else l) =
        coordDeriv0SAt (I := I) (fun x => X x) x₀ (fun x => A x)
          (fun q : Fin 2 => if q = 0 then l else j) := by
    unfold coordDeriv0SAt
    congr 2
    funext y
    have hslots :
        (fun a : Fin 2 => coordinateFrameAt (I := I) x₀ (if a = 0 then j else l) y) =
          (fun q : Fin 2 =>
            if q = 0 then coordinateFrameAt (I := I) x₀ j y
            else coordinateFrameAt (I := I) x₀ l y) := by
      funext q
      by_cases hq : q = 0 <;> simp [hq]
    have hslots' :
        (fun a : Fin 2 => coordinateFrameAt (I := I) x₀ (if a = 0 then l else j) y) =
          (fun q : Fin 2 =>
            if q = 0 then coordinateFrameAt (I := I) x₀ l y
            else coordinateFrameAt (I := I) x₀ j y) := by
      funext q
      by_cases hq : q = 0 <;> simp [hq]
    rw [hslots, hslots']
    exact hsymm y _ _
  have hcomp (a b : CoordinateIdx (𝕜 := 𝕜) E) :
      coordComponent0SAt (I := I) (A x₀)
          (fun q : Fin 2 => if q = 0 then a else b) =
        coordComponent0SAt (I := I) (A x₀)
          (fun q : Fin 2 => if q = 0 then b else a) := by
    simp only [coordComponent0SAt, component0S]
    have hslots :
        (fun q : Fin 2 => coordinateFrameAt_toBasis (I := I) x₀ (if q = 0 then a else b)) =
          (fun q : Fin 2 =>
            if q = 0 then coordinateFrameAt_toBasis (I := I) x₀ a
            else coordinateFrameAt_toBasis (I := I) x₀ b) := by
      funext q
      by_cases hq : q = 0 <;> simp [hq]
    have hslots' :
        (fun q : Fin 2 => coordinateFrameAt_toBasis (I := I) x₀ (if q = 0 then b else a)) =
          (fun q : Fin 2 =>
            if q = 0 then coordinateFrameAt_toBasis (I := I) x₀ b
            else coordinateFrameAt_toBasis (I := I) x₀ a) := by
      funext q
      by_cases hq : q = 0 <;> simp [hq]
    rw [hslots, hslots']
    exact hsymm x₀ _ _
  have hsum_left :
      (∑ k : CoordinateIdx (𝕜 := 𝕜) E,
        christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
          (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
          x₀ (X x₀) j k *
          coordComponent0SAt (I := I) (A x₀)
            (fun q : Fin 2 => if q = 0 then k else l)) =
      (∑ k : CoordinateIdx (𝕜 := 𝕜) E,
        christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
          (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
          x₀ (X x₀) j k *
          coordComponent0SAt (I := I) (A x₀)
            (fun q : Fin 2 => if q = 0 then l else k)) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hcomp k l]
  have hsum_right :
      (∑ k : CoordinateIdx (𝕜 := 𝕜) E,
        christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
          (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
          x₀ (X x₀) l k *
          coordComponent0SAt (I := I) (A x₀)
            (fun q : Fin 2 => if q = 0 then j else k)) =
      (∑ k : CoordinateIdx (𝕜 := 𝕜) E,
        christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
          (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
          x₀ (X x₀) l k *
          coordComponent0SAt (I := I) (A x₀)
            (fun q : Fin 2 => if q = 0 then k else j)) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hcomp j k]
  rw [hleft, hright]
  rw [hD, hsum_left, hsum_right]
  ring



omit h_mfd in
theorem nabla0SFun_two_symm_of_symm [IsManifold I ∞ M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (A : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2)
    (x₀ : M)
    (hsymm : ∀ y : M, ∀ U V : TangentSpace I y,
      A y (fun q : Fin 2 => if q = 0 then U else V) =
        A y (fun q : Fin 2 => if q = 0 then V else U))
    (Y Z : TangentSpace I x₀) :
    (nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      2 cov X A x₀) (fun q : Fin 2 => if q = 0 then Y else Z) =
      (nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        2 cov X A x₀) (fun q : Fin 2 => if q = 0 then Z else Y) := by
  apply tensor0S_two_symm_of_coordFrame (I := I)
    (coordinateFrameAt_toBasis (I := I) x₀)
  intro j l
  simpa [coordinateFrameAt_toBasis_apply] using
    nabla0SFun_two_eval_coordFrame_symm_of_symm
      (I := I) cov X A x₀ (modelDeriv_eq_coordDeriv0SAt (I := I) X x₀ A) hsymm j l



omit h_mfd in
theorem nabla0SFun_two_eval_coordFrame_expanded [IsManifold I ∞ M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (A : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2)
    (x₀ : M) (hderiv : ModelDerivEqCoordDeriv0SAt (I := I) X x₀ (fun x => A x))
    (Y Z : TangentSpace I x₀) :
    (nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      2 cov X A x₀) (fun q : Fin 2 => if q = 0 then Y else Z) =
      ∑ j : CoordinateIdx (𝕜 := 𝕜) E, ∑ l : CoordinateIdx (𝕜 := 𝕜) E,
        (coordinateFrameAt_toBasis (I := I) x₀).coord j Y *
          (coordinateFrameAt_toBasis (I := I) x₀).coord l Z *
          (coordDeriv0SAt (I := I) (fun x => X x) x₀ (fun x => A x)
              (fun q : Fin 2 => if q = 0 then j else l) -
            ∑ k : CoordinateIdx (𝕜 := 𝕜) E,
              christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
                (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
                x₀ (X x₀) j k *
                coordComponent0SAt (I := I) (A x₀)
                  (fun q : Fin 2 => if q = 0 then k else l) -
            ∑ k : CoordinateIdx (𝕜 := 𝕜) E,
              christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
                (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
                x₀ (X x₀) l k *
                coordComponent0SAt (I := I) (A x₀)
                  (fun q : Fin 2 => if q = 0 then j else k)) := by
  classical
  rw [tensor0S_two_eval_coordFrame_sum (I := I)
    ((nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      2 cov X A x₀)) Y Z]
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [nabla0SFun_two_eval_coordFrame (I := I) cov X A x₀ hderiv j l]

end TopRegularity

end DifferentialGeometry.Tensor.Coordinates
