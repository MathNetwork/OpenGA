import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureAlgebra
import DifferentialGeometry.Geometry.Curvature.Components.Basic
import DifferentialGeometry.Geometry.Curvature.Components.Lowering
import DifferentialGeometry.Geometry.Curvature.Components.TraceOneForm
import DifferentialGeometry.Geometry.Curvature.Components.RicciTrace
import DifferentialGeometry.Geometry.Curvature.Components.LocalFrame
import DifferentialGeometry.Geometry.Curvature.Components.Christoffel
import DifferentialGeometry.Geometry.Curvature.Components.RicciIdentity
import DifferentialGeometry.Geometry.Connection.LeviCivita.Curvature.LeviCivita
import DifferentialGeometry.Geometry.Connection.LeviCivita.Curvature.Realized
import DifferentialGeometry.Tensor.RSTensor.CotangentRiemannian

set_option autoImplicit false
set_option linter.style.longLine false













noncomputable section

namespace DifferentialGeometry.Integral.Connection

open DifferentialGeometry.Integral.Connection Tensor0SBundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {x : M}


def OrthonormalBasisAt
    (g : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x)) : Prop :=
  forall i j : Fin 3, g.inner x (basis i) (basis j) = delta3 i j



def standardRmCompAt
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (Rm04 : Tensor04At (I := I) (M := M) x)
    (i j k l : Fin 3) : Real :=
  rm04CompAt (I := I) basis Rm04 i j k l


def RicciSymAt
    (Ric : Tensor02At (I := I) (M := M) x) : Prop :=
  forall X Y : TangentSpace I x,
    Ric (vec2 X Y) = Ric (vec2 Y X)

private theorem sum_fin_two_fun {Idx : Type*} [Fintype Idx]
    {α : Type*} [AddCommMonoid α]
    (F : (Fin 2 -> Idx) -> α) :
    (∑ I0 : Fin 2 -> Idx, F I0) =
      ∑ i : Idx, ∑ j : Idx, F (fun a : Fin 2 => if a = 0 then i else j) := by
  classical
  rw [Fintype.sum_equiv (finTwoArrowEquiv Idx) F
    (fun p : Idx × Idx => F (fun a : Fin 2 => if a = 0 then p.1 else p.2))]
  · rw [Fintype.sum_prod_type]
  · intro I0
    congr
    funext a
    fin_cases a <;> simp [finTwoArrowEquiv]

private def fin4SlotsEquiv :
    (Fin 4 -> Fin 3) ≃ (((Fin 3 × Fin 3) × Fin 3) × Fin 3) where
  toFun f := (((f 0, f 1), f 2), f 3)
  invFun p := slots4 p.1.1.1 p.1.1.2 p.1.2 p.2
  left_inv f := by
    funext a
    fin_cases a <;> simp [slots4]
  right_inv p := by
    rcases p with ⟨⟨⟨i, j⟩, k⟩, l⟩
    simp [slots4]

private theorem sum_fin_four_fun {α : Type*} [AddCommMonoid α]
    (F : (Fin 4 -> Fin 3) -> α) :
    (∑ I0 : Fin 4 -> Fin 3, F I0) =
      ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
        F (slots4 i j k l) := by
  classical
  rw [Fintype.sum_equiv fin4SlotsEquiv F
    (fun p : (((Fin 3 × Fin 3) × Fin 3) × Fin 3) =>
      F (slots4 p.1.1.1 p.1.1.2 p.1.2 p.2))]
  · repeat rw [Fintype.sum_prod_type]
  · intro I0
    have hslot :
        slots4 (fin4SlotsEquiv I0).1.1.1 (fin4SlotsEquiv I0).1.1.2
            (fin4SlotsEquiv I0).1.2 (fin4SlotsEquiv I0).2 = I0 := by
      change fin4SlotsEquiv.symm (fin4SlotsEquiv I0) = I0
      exact fin4SlotsEquiv.left_inv I0
    rw [hslot]

omit [FiniteDimensional ℝ E] in
private theorem inner_eq_sum_repr3
    {g : SmoothRiemannianMetric I M}
    {basis : Module.Basis (Fin 3) Real (TangentSpace I x)}
    (horth : OrthonormalBasisAt (I := I) g x basis)
    (X Y : TangentSpace I x) :
    g.inner x X Y =
      ∑ i : Fin 3, basis.repr X i * basis.repr Y i := by
  calc
    g.inner x X Y =
        tangentFlatLinear_gen (I := I) g x
          (∑ i : Fin 3, basis.repr X i • basis i) Y := by
          rw [basis.sum_repr X]
          rfl
    _ = ∑ i : Fin 3, ∑ j : Fin 3,
        basis.repr X i * basis.repr Y j * g.inner x (basis i) (basis j) := by
          rw [map_sum]
          simp only [LinearMap.coe_sum, Finset.sum_apply]
          apply Finset.sum_congr rfl
          intro i _hi
          rw [map_smul]
          change (basis.repr X i) *
              g.inner x (basis i) Y =
            ∑ j : Fin 3,
              basis.repr X i * basis.repr Y j *
                g.inner x (basis i) (basis j)
          rw [show Y = ∑ j : Fin 3, basis.repr Y j • basis j by
            rw [basis.sum_repr Y]]
          rw [map_sum]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _hj
          simp [map_smul, smul_eq_mul, mul_assoc]
    _ = ∑ i : Fin 3, basis.repr X i * basis.repr Y i := by
          have h00 := horth 0 0
          have h01 := horth 0 1
          have h02 := horth 0 2
          have h10 := horth 1 0
          have h11 := horth 1 1
          have h12 := horth 1 2
          have h20 := horth 2 0
          have h21 := horth 2 1
          have h22 := horth 2 2
          simp [Fin.sum_univ_three, delta3, h00, h01, h02, h10, h11, h12, h20, h21, h22]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
private theorem vec2_update_zero {x : M}
    (X Y X' : TangentSpace I x) :
    Function.update (vec2 (I := I) X Y) (0 : Fin 2) X' =
      vec2 (I := I) X' Y := by
  funext a
  fin_cases a <;> simp [DifferentialGeometry.Integral.Connection.vec2, Function.update]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
private theorem vec2_update_one {x : M}
    (X Y Y' : TangentSpace I x) :
    Function.update (vec2 (I := I) X Y) (1 : Fin 2) Y' =
      vec2 (I := I) X Y' := by
  funext a
  fin_cases a <;> simp [DifferentialGeometry.Integral.Connection.vec2, Function.update]


omit [FiniteDimensional ℝ E] in
theorem ricciSym_of_basis
    {Idx : Type*} [Finite Idx]
    {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (Ric : Tensor02At (I := I) (M := M) x)
    (hsym : ∀ i j : Idx,
      Ric (vec2 (I := I) (basis i) (basis j)) =
        Ric (vec2 (I := I) (basis j) (basis i))) :
    RicciSymAt (I := I) Ric := by
  classical
  letI : Fintype Idx := Fintype.ofFinite Idx
  intro X Y
  let cx : Idx -> Real := fun i => basis.repr X i
  let cy : Idx -> Real := fun i => basis.repr Y i
  have hX : X = ∑ i : Idx, cx i • basis i := by
    simp [cx]
  have hY : Y = ∑ i : Idx, cy i • basis i := by
    simp [cy]
  have hXY :
      Ric (vec2 (I := I) X Y) =
        ∑ r : Fin 2 -> Idx,
          Ric (fun a : Fin 2 =>
            (if a = 0 then cx (r a) else cy (r a)) • basis (r a)) := by
    rw [hX, hY]
    have hsum :
        Ric (fun a : Fin 2 =>
            ∑ j : Idx,
              (if a = 0 then cx j else cy j) • basis j) =
          ∑ r : Fin 2 -> Idx,
            Ric (fun a : Fin 2 =>
              (if a = 0 then cx (r a) else cy (r a)) • basis (r a)) := by
      simpa using
        (ContinuousMultilinearMap.map_sum
          (f := Ric)
          (g := fun a j =>
            (if a = 0 then cx j else cy j) • basis j))
    simpa [vec2] using hsum
  have hYX :
      Ric (vec2 (I := I) Y X) =
        ∑ r : Fin 2 -> Idx,
          Ric (fun a : Fin 2 =>
            (if a = 0 then cy (r a) else cx (r a)) • basis (r a)) := by
    rw [hX, hY]
    have hsum :
        Ric (fun a : Fin 2 =>
            ∑ j : Idx,
              (if a = 0 then cy j else cx j) • basis j) =
          ∑ r : Fin 2 -> Idx,
            Ric (fun a : Fin 2 =>
              (if a = 0 then cy (r a) else cx (r a)) • basis (r a)) := by
      simpa using
        (ContinuousMultilinearMap.map_sum
          (f := Ric)
          (g := fun a j =>
            (if a = 0 then cy j else cx j) • basis j))
    simpa [vec2] using hsum
  rw [hXY, hYX]
  rw [sum_fin_two_fun, sum_fin_two_fun]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  have hleft :
      (fun a : Fin 2 =>
        (if a = 0
          then cx ((fun a : Fin 2 => if a = 0 then j else i) a)
          else cy ((fun a : Fin 2 => if a = 0 then j else i) a)) •
            basis ((fun a : Fin 2 => if a = 0 then j else i) a)) =
        vec2 (I := I) (cx j • basis j) (cy i • basis i) := by
    funext a
    fin_cases a <;> simp [vec2, DifferentialGeometry.Integral.Connection.vec2]
  have hright :
      (fun a : Fin 2 =>
        (if a = 0
          then cy ((fun a : Fin 2 => if a = 0 then i else j) a)
          else cx ((fun a : Fin 2 => if a = 0 then i else j) a)) •
            basis ((fun a : Fin 2 => if a = 0 then i else j) a)) =
        vec2 (I := I) (cy i • basis i) (cx j • basis j) := by
    funext a
    fin_cases a <;> simp [vec2, DifferentialGeometry.Integral.Connection.vec2]
  rw [hleft, hright]
  have hL :
      Ric (vec2 (I := I) (cx j • basis j) (cy i • basis i)) =
        (cx j) * (cy i) *
          Ric (vec2 (I := I) (basis j) (basis i)) := by
    have h0 := Ric.map_update_smul
      (vec2 (I := I) (basis j) (cy i • basis i))
      (0 : Fin 2) (cx j) (basis j)
    have h1 := Ric.map_update_smul
      (vec2 (I := I) (basis j) (basis i))
      (1 : Fin 2) (cy i) (basis i)
    calc
      Ric (vec2 (I := I) (cx j • basis j) (cy i • basis i))
          = (cx j) *
              Ric (vec2 (I := I) (basis j) (cy i • basis i)) := by
              simpa only [vec2, DifferentialGeometry.Integral.Connection.vec2, vec2_update_zero,
                smul_eq_mul] using h0
      _ = (cx j) * ((cy i) *
              Ric (vec2 (I := I) (basis j) (basis i))) := by
              congr 1
              simpa only [vec2, DifferentialGeometry.Integral.Connection.vec2, vec2_update_one,
                smul_eq_mul] using h1
      _ = (cx j) * (cy i) *
              Ric (vec2 (I := I) (basis j) (basis i)) := by ring
  have hR :
      Ric (vec2 (I := I) (cy i • basis i) (cx j • basis j)) =
        (cy i) * (cx j) *
          Ric (vec2 (I := I) (basis i) (basis j)) := by
    have h0 := Ric.map_update_smul
      (vec2 (I := I) (basis i) (cx j • basis j))
      (0 : Fin 2) (cy i) (basis i)
    have h1 := Ric.map_update_smul
      (vec2 (I := I) (basis i) (basis j))
      (1 : Fin 2) (cx j) (basis j)
    calc
      Ric (vec2 (I := I) (cy i • basis i) (cx j • basis j))
          = (cy i) *
              Ric (vec2 (I := I) (basis i) (cx j • basis j)) := by
              simpa only [vec2, DifferentialGeometry.Integral.Connection.vec2, vec2_update_zero,
                smul_eq_mul] using h0
      _ = (cy i) * ((cx j) *
              Ric (vec2 (I := I) (basis i) (basis j))) := by
              congr 1
              simpa only [vec2, DifferentialGeometry.Integral.Connection.vec2, vec2_update_one,
                smul_eq_mul] using h1
      _ = (cy i) * (cx j) *
              Ric (vec2 (I := I) (basis i) (basis j)) := by ring
  rw [hL, hR, hsym j i]
  ring


def RicciNonnegAt
    (Ric : Tensor02At (I := I) (M := M) x) : Prop :=
  forall X : TangentSpace I x, 0 <= Ric (vec2 X X)


def ricciCovAt
    (Ric : Tensor02At (I := I) (M := M) x)
    (X : TangentSpace I x) :
    Module.Dual Real (TangentSpace I x) where
  toFun := fun Y => Ric (vec2 X Y)
  map_add' := by
    intro Y Z
    classical
    let m : Fin 2 -> TangentSpace I x := vec2 X Y
    have hmap := Ric.map_update_add m 1 Y Z
    have hleft :
        Function.update m (1 : Fin 2) (Y + Z) = vec2 X (Y + Z) := by
      funext i
      fin_cases i <;> simp [m, DifferentialGeometry.Integral.Connection.vec2, Function.update]
    have hY : Function.update m (1 : Fin 2) Y = vec2 X Y := by
      funext i
      fin_cases i <;> simp [m, DifferentialGeometry.Integral.Connection.vec2, Function.update]
    have hZ : Function.update m (1 : Fin 2) Z = vec2 X Z := by
      funext i
      fin_cases i <;> simp [m, DifferentialGeometry.Integral.Connection.vec2, Function.update]
    simpa [hleft, hY, hZ] using hmap
  map_smul' := by
    intro c Y
    classical
    let m : Fin 2 -> TangentSpace I x := vec2 X Y
    have hmap := Ric.map_update_smul m 1 c Y
    have hleft :
        Function.update m (1 : Fin 2) (c • Y) = vec2 X (c • Y) := by
      funext i
      fin_cases i <;> simp [m, DifferentialGeometry.Integral.Connection.vec2, Function.update]
    have hY : Function.update m (1 : Fin 2) Y = vec2 X Y := by
      funext i
      fin_cases i <;> simp [m, DifferentialGeometry.Integral.Connection.vec2, Function.update]
    simpa [hleft, hY] using hmap

omit [FiniteDimensional ℝ E] in
private theorem ricciCovAt_add
    (Ric : Tensor02At (I := I) (M := M) x)
    (X Y : TangentSpace I x) :
    ricciCovAt (I := I) Ric (X + Y) =
      ricciCovAt (I := I) Ric X + ricciCovAt (I := I) Ric Y := by
  ext Z
  classical
  let m : Fin 2 -> TangentSpace I x := vec2 X Z
  have hmap := Ric.map_update_add m 0 X Y
  have hleft :
      Function.update m (0 : Fin 2) (X + Y) = vec2 (X + Y) Z := by
    funext i
    fin_cases i <;> simp [m, DifferentialGeometry.Integral.Connection.vec2, Function.update]
  have hX : Function.update m (0 : Fin 2) X = vec2 X Z := by
    funext i
    fin_cases i <;> simp [m, DifferentialGeometry.Integral.Connection.vec2, Function.update]
  have hY : Function.update m (0 : Fin 2) Y = vec2 Y Z := by
    funext i
    fin_cases i <;> simp [m, DifferentialGeometry.Integral.Connection.vec2, Function.update]
  simpa [ricciCovAt, hleft, hX, hY] using hmap

omit [FiniteDimensional ℝ E] in
private theorem ricciCovAt_smul
    (Ric : Tensor02At (I := I) (M := M) x)
    (c : Real) (X : TangentSpace I x) :
    ricciCovAt (I := I) Ric (c • X) =
      c • ricciCovAt (I := I) Ric X := by
  ext Z
  classical
  let m : Fin 2 -> TangentSpace I x := vec2 X Z
  have hmap := Ric.map_update_smul m 0 c X
  have hleft :
      Function.update m (0 : Fin 2) (c • X) = vec2 (c • X) Z := by
    funext i
    fin_cases i <;> simp [m, DifferentialGeometry.Integral.Connection.vec2, Function.update]
  have hX : Function.update m (0 : Fin 2) X = vec2 X Z := by
    funext i
    fin_cases i <;> simp [m, DifferentialGeometry.Integral.Connection.vec2, Function.update]
  simpa [ricciCovAt, hleft, hX] using hmap


def ricciEndAt
    (g : SmoothRiemannianMetric I M)
    (Ric : Tensor02At (I := I) (M := M) x) :
    TangentSpace I x →ₗ[Real] TangentSpace I x where
  toFun := fun X =>
    cotangentSharp_gen (I := I) g x
      (dualToCotangent_gen (I := I) (ricciCovAt (I := I) Ric X))
  map_add' := by
    intro X Y
    change
      cotangentSharpLinear_gen (I := I) g x
          (dualToCotangent_gen (I := I) (ricciCovAt (I := I) Ric (X + Y))) =
        cotangentSharpLinear_gen (I := I) g x
          (dualToCotangent_gen (I := I) (ricciCovAt (I := I) Ric X)) +
          cotangentSharpLinear_gen (I := I) g x
          (dualToCotangent_gen (I := I) (ricciCovAt (I := I) Ric Y))
    rw [ricciCovAt_add (I := I) Ric X Y]
    change
      cotangentSharpLinear_gen (I := I) g x
          (dualToCotangentLinear (I := I)
            (ricciCovAt (I := I) Ric X + ricciCovAt (I := I) Ric Y)) =
        cotangentSharpLinear_gen (I := I) g x
          (dualToCotangentLinear (I := I) (ricciCovAt (I := I) Ric X)) +
          cotangentSharpLinear_gen (I := I) g x
          (dualToCotangentLinear (I := I) (ricciCovAt (I := I) Ric Y))
    rw [map_add, map_add]
  map_smul' := by
    intro c X
    change
      cotangentSharpLinear_gen (I := I) g x
          (dualToCotangent_gen (I := I) (ricciCovAt (I := I) Ric (c • X))) =
        c • cotangentSharpLinear_gen (I := I) g x
          (dualToCotangent_gen (I := I) (ricciCovAt (I := I) Ric X))
    rw [ricciCovAt_smul (I := I) Ric c X]
    change
      cotangentSharpLinear_gen (I := I) g x
          (dualToCotangentLinear (I := I)
            (c • ricciCovAt (I := I) Ric X)) =
        c • cotangentSharpLinear_gen (I := I) g x
          (dualToCotangentLinear (I := I) (ricciCovAt (I := I) Ric X))
    rw [map_smul, map_smul]

theorem ricciEnd_inner
    (g : SmoothRiemannianMetric I M)
    (Ric : Tensor02At (I := I) (M := M) x)
    (X Y : TangentSpace I x) :
    g.inner x (ricciEndAt (I := I) g Ric X) Y = Ric (vec2 X Y) := by
  simp [ricciEndAt, ricciCovAt, cotangentSharp_inner_gen]

omit [FiniteDimensional ℝ E] in
@[simp]
theorem standardRmCompAt_apply
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (Rm04 : Tensor04At (I := I) (M := M) x)
    (i j k l : Fin 3) :
    standardRmCompAt basis Rm04 i j k l =
      rm04CompAt (I := I) basis Rm04 i j k l := rfl








omit [FiniteDimensional ℝ E] in
theorem rm04Comp_displayedRiemannFromRicci3D_at_of_curvature_symmetries
    {basis : Module.Basis (Fin 3) Real (TangentSpace I x)}
    {Rm04 : Tensor04At (I := I) (M := M) x}
    (h : AlgebraicCurvatureSymmetries3 (standardRmCompAt basis Rm04)) :
    forall i j k l : Fin 3,
      rm04CompAt (I := I) basis Rm04 i j l k =
        stdRicci3 (standardRmCompAt basis Rm04) i l * delta3 j k
          - stdRicci3 (standardRmCompAt basis Rm04) j l * delta3 i k
          - stdRicci3 (standardRmCompAt basis Rm04) i k * delta3 j l
          + stdRicci3 (standardRmCompAt basis Rm04) j k * delta3 i l
          - (1 / 2 : Real) * stdScalar3 (standardRmCompAt basis Rm04) *
              (delta3 i l * delta3 j k - delta3 j l * delta3 i k) := by
  intro i j k l
  have hformula :=
    displayedRiemannFromRicci3D_of_algebraic_curvature_symmetries
      h i j k l
  simpa [displayedRiemannFromRicciRhs3, standardRmCompAt_apply] using hformula



theorem rm04Comp_displayedRiemannFromRicci3D_frame_of_curvature_symmetries
    {Rm04 : Tensor04Section (I := I) (M := M)}
    {u : Set M}
    {frame : Fin 3 -> (x : M) -> TangentSpace I x}
    (hframe : IsLocalFrameOn I E ∞ frame u)
    {x : M} (hx : x ∈ u)
    (h : AlgebraicCurvatureSymmetries3
      (standardRmCompAt (I := I) (M := M) (hframe.toBasisAt hx) (Rm04 x))) :
    forall i j k l : Fin 3,
      rm04CompAt (I := I) (hframe.toBasisAt hx) (Rm04 x) i j l k =
        stdRicci3 (standardRmCompAt (I := I) (M := M)
          (hframe.toBasisAt hx) (Rm04 x)) i l * delta3 j k
          - stdRicci3 (standardRmCompAt (I := I) (M := M)
            (hframe.toBasisAt hx) (Rm04 x)) j l * delta3 i k
          - stdRicci3 (standardRmCompAt (I := I) (M := M)
            (hframe.toBasisAt hx) (Rm04 x)) i k * delta3 j l
          + stdRicci3 (standardRmCompAt (I := I) (M := M)
            (hframe.toBasisAt hx) (Rm04 x)) j k * delta3 i l
          - (1 / 2 : Real) * stdScalar3 (standardRmCompAt (I := I) (M := M)
            (hframe.toBasisAt hx) (Rm04 x)) *
              (delta3 i l * delta3 j k - delta3 j l * delta3 i k) :=
  rm04Comp_displayedRiemannFromRicci3D_at_of_curvature_symmetries
    (I := I) h



theorem algebraicCurvatureSymmetries3_standardRmCompAt_of_leviCivita_realizes
    [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M] [SigmaCompactSpace M] [T2Space M]
    (g : SmoothRiemannianMetric I M)
    (Rm04 : Tensor04Section (I := I) (M := M))
    (hRm04 : Rm04RealizesConnection (I := I) g
      (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) g) Rm04)
    {x : M} (basis : Module.Basis (Fin 3) Real (TangentSpace I x)) :
    AlgebraicCurvatureSymmetries3 (standardRmCompAt (I := I) basis (Rm04 x)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j k l
    simpa [standardRmCompAt_apply] using
      (DifferentialGeometry.Integral.Connection.rm04InputSkewAt_of_leviCivita_realizes
        (I := I) g Rm04 hRm04 (basis i) (basis j) (basis k) (basis l))
  · intro i j k l
    have h :=
      DifferentialGeometry.Integral.Connection.rm04OutputSkewAt_of_leviCivita_realizes
        (I := I) g Rm04 hRm04 (basis i) (basis j) (basis k) (basis l)
    have h' :
        (Rm04 x) (vec4 (basis i) (basis j) (basis l) (basis k)) =
          -(Rm04 x) (vec4 (basis i) (basis j) (basis k) (basis l)) := by
      linarith
    simpa [standardRmCompAt_apply] using h'
  · intro i j k l
    simpa [standardRmCompAt_apply] using
      (DifferentialGeometry.Integral.Connection.rm04PairSymmAt_of_leviCivita_realizes
        (I := I) g Rm04 hRm04 (basis i) (basis j) (basis k) (basis l)).symm



theorem rm04Comp_displayedRiemannFromRicci3D_at_of_leviCivita_realizes
    [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M] [SigmaCompactSpace M] [T2Space M]
    (g : SmoothRiemannianMetric I M)
    (Rm04 : Tensor04Section (I := I) (M := M))
    (hRm04 : Rm04RealizesConnection (I := I) g
      (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) g) Rm04)
    {x : M} (basis : Module.Basis (Fin 3) Real (TangentSpace I x)) :
    forall i j k l : Fin 3,
      rm04CompAt (I := I) basis (Rm04 x) i j l k =
        stdRicci3 (standardRmCompAt (I := I) basis (Rm04 x)) i l * delta3 j k
          - stdRicci3 (standardRmCompAt (I := I) basis (Rm04 x)) j l * delta3 i k
          - stdRicci3 (standardRmCompAt (I := I) basis (Rm04 x)) i k * delta3 j l
          + stdRicci3 (standardRmCompAt (I := I) basis (Rm04 x)) j k * delta3 i l
          - (1 / 2 : Real) * stdScalar3 (standardRmCompAt (I := I) basis (Rm04 x)) *
              (delta3 i l * delta3 j k - delta3 j l * delta3 i k) :=
  rm04Comp_displayedRiemannFromRicci3D_at_of_curvature_symmetries (I := I)
    (algebraicCurvatureSymmetries3_standardRmCompAt_of_leviCivita_realizes
      (I := I) g Rm04 hRm04 basis)






structure RiemannFromRicci3DTraceDataAt
    (g : SmoothRiemannianMetric I M)
    (Ric : Tensor02At (I := I) (M := M) x)
    (scalar : Real)
    (Rm04 : Tensor04At (I := I) (M := M) x)
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x)) : Prop where
  orthonormal : OrthonormalBasisAt g x basis
  curvature_symmetries :
    AlgebraicCurvatureSymmetries3 (standardRmCompAt basis Rm04)
  ricci_trace : forall i j : Fin 3,
    ricciCompAt (I := I) basis Ric i j =
      stdRicci3 (standardRmCompAt basis Rm04) i j
  scalar_trace :
    scalar = stdScalar3 (standardRmCompAt basis Rm04)







omit [FiniteDimensional ℝ E] in
theorem firstTrace_delta3_eq_neg_stdRicci3
    {Rm04 : Tensor04At (I := I) (M := M) x}
    {basis : Module.Basis (Fin 3) Real (TangentSpace I x)}
    (hcurv : AlgebraicCurvatureSymmetries3 (standardRmCompAt basis Rm04))
    (i j : Fin 3) :
    (∑ k : Fin 3, ∑ l : Fin 3,
        delta3 k l * Rm04 (vec4 (basis k) (basis i) (basis j) (basis l))) =
      -stdRicci3 (standardRmCompAt basis Rm04) i j := by
  have h0 := hcurv.anti_last 0 i 0 j
  have h1 := hcurv.anti_last 1 i 1 j
  have h2 := hcurv.anti_last 2 i 2 j
  have h0' :
      standardRmCompAt basis Rm04 0 i j 0 =
        -standardRmCompAt basis Rm04 0 i 0 j := by
    linarith
  have h1' :
      standardRmCompAt basis Rm04 1 i j 1 =
        -standardRmCompAt basis Rm04 1 i 1 j := by
    linarith
  have h2' :
      standardRmCompAt basis Rm04 2 i j 2 =
        -standardRmCompAt basis Rm04 2 i 2 j := by
    linarith
  have h0d :
      Rm04 (vec4 (basis 0) (basis i) (basis j) (basis 0)) =
        -Rm04 (vec4 (basis 0) (basis i) (basis 0) (basis j)) := by
    simpa [standardRmCompAt_apply, rm04CompAt_apply] using h0'
  have h1d :
      Rm04 (vec4 (basis 1) (basis i) (basis j) (basis 1)) =
        -Rm04 (vec4 (basis 1) (basis i) (basis 1) (basis j)) := by
    simpa [standardRmCompAt_apply, rm04CompAt_apply] using h1'
  have h2d :
      Rm04 (vec4 (basis 2) (basis i) (basis j) (basis 2)) =
        -Rm04 (vec4 (basis 2) (basis i) (basis 2) (basis j)) := by
    simpa [standardRmCompAt_apply, rm04CompAt_apply] using h2'
  rw [Fin.sum_univ_three]
  simp [delta3]
  rw [h0d, h1d, h2d]
  unfold stdRicci3
  simp [standardRmCompAt_apply, rm04CompAt_apply]
  ring







omit [FiniteDimensional ℝ E] in
theorem traceDataOfFirst
    {g : SmoothRiemannianMetric I M}
    {Ric : Tensor02At (I := I) (M := M) x}
    {scalar : Real}
    {Rm04 : Tensor04At (I := I) (M := M) x}
    {basis : Module.Basis (Fin 3) Real (TangentSpace I x)}
    (horth : OrthonormalBasisAt (I := I) g x basis)
    (hcurv : AlgebraicCurvatureSymmetries3 (standardRmCompAt basis Rm04))
    (hRic : RicciRealizesRm04FirstTraceAt (I := I) Ric Rm04 delta3 basis)
    (hScalar : ScalarRealizesRicciTraceAt (I := I) scalar Ric delta3 basis) :
    RiemannFromRicci3DTraceDataAt g (-Ric) (-scalar) Rm04 basis := by
  refine ⟨horth, hcurv, ?_, ?_⟩
  · intro i j
    rw [ricciCompAt_apply]
    have hfirst := firstTrace_delta3_eq_neg_stdRicci3
      (I := I) (M := M) hcurv i j
    have hRicij := hRic i j
    change -(Ric (vec2 (basis i) (basis j))) =
      stdRicci3 (standardRmCompAt basis Rm04) i j
    rw [hRicij]
    rw [hfirst]
    ring
  · have h00 := firstTrace_delta3_eq_neg_stdRicci3
      (I := I) (M := M) hcurv 0 0
    have h11 := firstTrace_delta3_eq_neg_stdRicci3
      (I := I) (M := M) hcurv 1 1
    have h22 := firstTrace_delta3_eq_neg_stdRicci3
      (I := I) (M := M) hcurv 2 2
    have hRic00 := hRic 0 0
    have hRic11 := hRic 1 1
    have hRic22 := hRic 2 2
    have hdiag0 :
        Ric (vec2 (basis 0) (basis 0)) =
          -stdRicci3 (standardRmCompAt basis Rm04) 0 0 := by
      rw [hRic00, h00]
    have hdiag1 :
        Ric (vec2 (basis 1) (basis 1)) =
          -stdRicci3 (standardRmCompAt basis Rm04) 1 1 := by
      rw [hRic11, h11]
    have hdiag2 :
        Ric (vec2 (basis 2) (basis 2)) =
          -stdRicci3 (standardRmCompAt basis Rm04) 2 2 := by
      rw [hRic22, h22]
    change -scalar = stdScalar3 (standardRmCompAt basis Rm04)
    rw [hScalar]
    simp [stdScalar3, Fin.sum_univ_three, delta3, hdiag0, hdiag1, hdiag2]
    ring







omit [FiniteDimensional ℝ E] in
theorem rm04Comp_displayedRiemannFromRicci3D_at
    {g : SmoothRiemannianMetric I M}
    {Ric : Tensor02At (I := I) (M := M) x}
    {scalar : Real}
    {Rm04 : Tensor04At (I := I) (M := M) x}
    {basis : Module.Basis (Fin 3) Real (TangentSpace I x)}
    (h : RiemannFromRicci3DTraceDataAt g Ric scalar Rm04 basis) :
    forall i j k l : Fin 3,
      rm04CompAt (I := I) basis Rm04 i j l k =
        ricciCompAt (I := I) basis Ric i l * delta3 j k
          - ricciCompAt (I := I) basis Ric j l * delta3 i k
          - ricciCompAt (I := I) basis Ric i k * delta3 j l
          + ricciCompAt (I := I) basis Ric j k * delta3 i l
          - (1 / 2 : Real) * scalar *
              (delta3 i l * delta3 j k - delta3 j l * delta3 i k) := by
  intro i j k l
  have hformula :=
    displayedRiemannFromRicci3D_of_algebraic_curvature_symmetries
      h.curvature_symmetries i j k l
  simp only [standardRmCompAt_apply] at hformula
  rw [hformula]
  unfold displayedRiemannFromRicciRhs3
  rw [← h.ricci_trace i l, ← h.ricci_trace j l, ← h.ricci_trace i k,
    ← h.ricci_trace j k, ← h.scalar_trace]




omit [FiniteDimensional ℝ E] in
theorem rm04Comp_einstein3_at
    {g : SmoothRiemannianMetric I M}
    {Ric : Tensor02At (I := I) (M := M) x}
    {scalar : Real}
    {Rm04 : Tensor04At (I := I) (M := M) x}
    {basis : Module.Basis (Fin 3) Real (TangentSpace I x)}
    (h : RiemannFromRicci3DTraceDataAt g Ric scalar Rm04 basis)
    (hEin : ∀ i j : Fin 3,
      ricciCompAt (I := I) basis Ric i j =
        (scalar / 3) * delta3 i j) :
    ∀ i j k l : Fin 3,
      rm04CompAt (I := I) basis Rm04 i j l k =
        (scalar / 6) *
          (delta3 i l * delta3 j k - delta3 j l * delta3 i k) := by
  intro i j k l
  rw [rm04Comp_displayedRiemannFromRicci3D_at (I := I) h i j k l]
  rw [hEin i l, hEin j l, hEin i k, hEin j k]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [delta3] <;> ring




theorem rm04_einstein3_at
    {g : SmoothRiemannianMetric I M}
    {Ric : Tensor02At (I := I) (M := M) x}
    {scalar : Real}
    {Rm04 : Tensor04At (I := I) (M := M) x}
    {basis : Module.Basis (Fin 3) Real (TangentSpace I x)}
    (h : RiemannFromRicci3DTraceDataAt g Ric scalar Rm04 basis)
    (hEin : ∀ i j : Fin 3,
      ricciCompAt (I := I) basis Ric i j =
        (scalar / 3) * delta3 i j)
    (X Y : TangentSpace I x) :
    Rm04 (vec4 (I := I) X Y Y X) =
      -(scalar / 6) *
        (g.inner x X X * g.inner x Y Y -
          g.inner x X Y * g.inner x X Y) := by
  classical
  have hcomp := rm04Comp_einstein3_at (I := I) h hEin
  have hcomp' : ∀ a b c d : Fin 3,
      rm04CompAt (I := I) basis Rm04 a b c d =
        (scalar / 6) *
          (delta3 a c * delta3 b d - delta3 b c * delta3 a d) := by
    intro a b c d
    simpa [mul_comm, mul_left_comm, mul_assoc] using hcomp a b d c
  have hcompSlots : ∀ a b c d : Fin 3,
      component0S (I := I) basis Rm04 (slots4 a b c d) =
        (scalar / 6) *
          (delta3 a c * delta3 b d - delta3 b c * delta3 a d) := by
    intro a b c d
    change rm04CompAt (I := I) basis Rm04 a b c d =
      (scalar / 6) *
        (delta3 a c * delta3 b d - delta3 b c * delta3 a d)
    exact hcomp' a b c d
  have hXX := inner_eq_sum_repr3 (I := I) h.orthonormal X X
  have hYY := inner_eq_sum_repr3 (I := I) h.orthonormal Y Y
  have hXY := inner_eq_sum_repr3 (I := I) h.orthonormal X Y
  rw [tensor0S_apply_eq_sum (I := I) basis Rm04 (vec4 (I := I) X Y Y X)]
  rw [sum_fin_four_fun]
  rw [hXX, hYY, hXY]
  simp_rw [hcompSlots]
  simp [slots4, DifferentialGeometry.Integral.Connection.vec4, delta3, Fin.sum_univ_three, Fin.prod_univ_four]
  ring







theorem rm04_firstTrace_einstein3_at
    {g : SmoothRiemannianMetric I M}
    {Ric : Tensor02At (I := I) (M := M) x}
    {scalar : Real}
    {Rm04 : Tensor04At (I := I) (M := M) x}
    {basis : Module.Basis (Fin 3) Real (TangentSpace I x)}
    (horth : OrthonormalBasisAt (I := I) g x basis)
    (hcurv : AlgebraicCurvatureSymmetries3 (standardRmCompAt basis Rm04))
    (hRic : RicciRealizesRm04FirstTraceAt (I := I) Ric Rm04 delta3 basis)
    (hScalar : ScalarRealizesRicciTraceAt (I := I) scalar Ric delta3 basis)
    (hEin : ∀ i j : Fin 3,
      ricciCompAt (I := I) basis Ric i j =
        (scalar / 3) * delta3 i j)
    (X Y : TangentSpace I x) :
    Rm04 (vec4 (I := I) X Y Y X) =
      (scalar / 6) *
        (g.inner x X X * g.inner x Y Y -
          g.inner x X Y * g.inner x X Y) := by
  classical
  have htrace :=
    traceDataOfFirst (I := I) (M := M) horth hcurv hRic hScalar
  have hEinNeg : ∀ i j : Fin 3,
      ricciCompAt (I := I) basis (-Ric) i j =
        ((-scalar) / 3) * delta3 i j := by
    intro i j
    have hij := hEin i j
    rw [ricciCompAt_apply] at hij
    rw [ricciCompAt_apply]
    change -(Ric (vec2 (basis i) (basis j))) =
      ((-scalar) / 3) * delta3 i j
    rw [hij]
    ring
  have hRm :=
    rm04_einstein3_at (I := I) htrace hEinNeg X Y
  rw [hRm]
  ring


theorem rm04Std_ein3_at
    {g : SmoothRiemannianMetric I M}
    {Ric : Tensor02At (I := I) (M := M) x}
    {scalar : Real}
    {Rm04 : Tensor04At (I := I) (M := M) x}
    {basis : Module.Basis (Fin 3) Real (TangentSpace I x)}
    (horth : OrthonormalBasisAt (I := I) g x basis)
    (hcurv : AlgebraicCurvatureSymmetries3 (standardRmCompAt basis Rm04))
    (hRic : RicciRealizesRm04FirstTraceAt (I := I) Ric Rm04 delta3 basis)
    (hScalar : ScalarRealizesRicciTraceAt (I := I) scalar Ric delta3 basis)
    (hEin : ∀ i j : Fin 3,
      ricciCompAt (I := I) basis Ric i j =
        (scalar / 3) * delta3 i j)
    (X Y : TangentSpace I x) :
    DifferentialGeometry.Integral.Connection.tensor04StdAt (I := I) (M := M) Rm04 X Y Y X =
      (scalar / 6) *
        (g.inner x X X * g.inner x Y Y -
          g.inner x X Y * g.inner x X Y) :=
  rm04_firstTrace_einstein3_at (I := I) horth hcurv hRic hScalar hEin X Y


theorem rm04Comp_displayedRiemannFromRicci3D_frame
    {g : SmoothRiemannianMetric I M}
    {Ric : Tensor02Section (I := I) (M := M)}
    {scalar : M -> Real}
    {Rm04 : Tensor04Section (I := I) (M := M)}
    {u : Set M}
    {frame : Fin 3 -> (x : M) -> TangentSpace I x}
    (hframe : IsLocalFrameOn I E ∞ frame u)
    {x : M} (hx : x ∈ u)
    (h : RiemannFromRicci3DTraceDataAt g (Ric x) (scalar x)
      (Rm04 x) (hframe.toBasisAt hx)) :
    forall i j k l : Fin 3,
      rm04CompAt (I := I) (hframe.toBasisAt hx) (Rm04 x) i j l k =
        ricciCompAt (I := I) (hframe.toBasisAt hx) (Ric x) i l * delta3 j k
          - ricciCompAt (I := I) (hframe.toBasisAt hx) (Ric x) j l * delta3 i k
          - ricciCompAt (I := I) (hframe.toBasisAt hx) (Ric x) i k * delta3 j l
          + ricciCompAt (I := I) (hframe.toBasisAt hx) (Ric x) j k * delta3 i l
          - (1 / 2 : Real) * scalar x *
              (delta3 i l * delta3 j k - delta3 j l * delta3 i k) :=
  rm04Comp_displayedRiemannFromRicci3D_at (I := I) h






theorem rm04_kn_gform
    {g : SmoothRiemannianMetric I M}
    {Ric : Tensor02At (I := I) (M := M) x}
    {scalar : Real}
    {Rm04 : Tensor04At (I := I) (M := M) x}
    {basis : Module.Basis (Fin 3) Real (TangentSpace I x)}
    (h : RiemannFromRicci3DTraceDataAt g Ric scalar Rm04 basis)
    (X Y Z W : TangentSpace I x) :
    Rm04 (vec4 (I := I) X Y Z W) =
      Ric (vec2 (I := I) X Z) * g.inner x Y W
        - Ric (vec2 (I := I) Y Z) * g.inner x X W
        - Ric (vec2 (I := I) X W) * g.inner x Y Z
        + Ric (vec2 (I := I) Y W) * g.inner x X Z
        - (scalar / 2) *
            (g.inner x X Z * g.inner x Y W - g.inner x Y Z * g.inner x X W) := by
  classical
  have horth := h.orthonormal

  have hcomp : ∀ a b c d : Fin 3,
      component0S (I := I) basis Rm04 (slots4 a b c d) =
        ricciCompAt (I := I) basis Ric a c * delta3 b d
          - ricciCompAt (I := I) basis Ric b c * delta3 a d
          - ricciCompAt (I := I) basis Ric a d * delta3 b c
          + ricciCompAt (I := I) basis Ric b d * delta3 a c
          - (1 / 2 : Real) * scalar *
              (delta3 a c * delta3 b d - delta3 b c * delta3 a d) := by
    intro a b c d
    have hd := rm04Comp_displayedRiemannFromRicci3D_at (I := I) h a b d c
    simpa [rm04CompAt] using hd

  have hg : ∀ P Q : TangentSpace I x,
      g.inner x P Q = ∑ i : Fin 3, basis.repr P i * basis.repr Q i :=
    fun P Q => inner_eq_sum_repr3 (I := I) horth P Q
  have hric : ∀ P Q : TangentSpace I x,
      Ric (vec2 (I := I) P Q) =
        ∑ a : Fin 3, ∑ c : Fin 3,
          ricciCompAt (I := I) basis Ric a c * (basis.repr P a * basis.repr Q c) := by
    intro P Q
    rw [tensor0S_apply_eq_sum (I := I) basis Ric (vec2 (I := I) P Q), sum_fin_two_fun]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
    simp [ricciCompAt, slots2, DifferentialGeometry.Integral.Connection.vec2,
      Fin.prod_univ_two, Module.Basis.coord_apply, mul_comm, mul_assoc]

  rw [tensor0S_apply_eq_sum (I := I) basis Rm04 (vec4 (I := I) X Y Z W), sum_fin_four_fun]
  simp_rw [hcomp, hg, hric]
  simp [DifferentialGeometry.Integral.Connection.vec4, slots4, Fin.prod_univ_four,
    Module.Basis.coord_apply, delta3, Fin.sum_univ_three]
  ring

end DifferentialGeometry.Integral.Connection
