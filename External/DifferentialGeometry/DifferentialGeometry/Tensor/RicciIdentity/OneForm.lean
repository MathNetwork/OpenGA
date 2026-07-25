import DifferentialGeometry.Geometry.Operator.RoughLaplacian
import DifferentialGeometry.Geometry.Curvature.Realized.CurvatureTensor
import DifferentialGeometry.Tensor.RicciIdentity.MixedComponents
import DifferentialGeometry.Tensor.Auxiliary.SlotAlgebra
import DifferentialGeometry.Tensor.RSTensor.CurvatureAction
import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.HigherOrder
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false










noncomputable section

namespace DifferentialGeometry.Integral.Connection

open Bundle Tensor0SBundle
open DifferentialGeometry.Tensor.SlotAlgebra
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]



abbrev Tensor0SSection (s : ℕ) :=
  Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    (∞ : WithTop ℕ∞) s


abbrev OneFormSection :=
  Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    (∞ : WithTop ℕ∞) 1


abbrev TwoTensorSection :=
  Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    (∞ : WithTop ℕ∞) 2



def NablaOneFormRealizesAt
    [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (alpha : OneFormSection (I := I) (M := M))
    (nablaAlpha : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (x : M) : Prop :=
  ∀ (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
      (Y : TangentSpace I x),
    nablaAlpha x (vec2 (X x) Y) =
      nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        1 cov X alpha x (fun _ : Fin 1 => Y)






def NablaOneFormSectionRealizes
    [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (alpha : OneFormSection (I := I) (M := M))
    (nablaAlpha : TwoTensorSection (I := I) (M := M)) : Prop :=
  ∀ x : M, NablaOneFormRealizesAt (I := I) cov alpha (fun y => nablaAlpha y) x




def Nabla2OneFormRealizesAt
    [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (alpha : OneFormSection (I := I) (M := M))
    (nablaAlpha : TwoTensorSection (I := I) (M := M))
    (x : M)
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x) :
    Prop :=
  NablaOneFormSectionRealizes (I := I) cov alpha nablaAlpha ∧
    ∀ (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
        (Y Z : TangentSpace I x),
      nabla2Alpha (vec3 (X x) Y Z) =
        nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          2 cov X nablaAlpha x (vec2 Y Z)

theorem nabla2OneFormRealizesAt_first
    [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (alpha : OneFormSection (I := I) (M := M))
    (nablaAlpha : TwoTensorSection (I := I) (M := M))
    (x : M)
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (h : Nabla2OneFormRealizesAt (I := I) cov alpha nablaAlpha x nabla2Alpha) :
    NablaOneFormSectionRealizes (I := I) cov alpha nablaAlpha :=
  h.1

theorem nabla2OneFormRealizesAt_apply
    [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (alpha : OneFormSection (I := I) (M := M))
    (nablaAlpha : TwoTensorSection (I := I) (M := M))
    (x : M)
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (h : Nabla2OneFormRealizesAt (I := I) cov alpha nablaAlpha x nabla2Alpha)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (Y Z : TangentSpace I x) :
    nabla2Alpha (vec3 (X x) Y Z) =
      nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 cov X nablaAlpha x (vec2 Y Z) :=
  h.2 X Y Z



theorem nabla2OneFormRealizesAt_of_totalNabla
    [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (alpha : OneFormSection (I := I) (M := M))
    (nablaAlpha : TwoTensorSection (I := I) (M := M))
    (nabla2AlphaSec :
      Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) 3)
    (h1 : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 1 cov alpha nablaAlpha)
    (h2 : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 2 cov nablaAlpha nabla2AlphaSec)
    (x : M) :
    Nabla2OneFormRealizesAt (I := I) cov alpha nablaAlpha x
      (nabla2AlphaSec x) := by
  constructor
  · intro y X Y
    have h := h1 X y (fun _ : Fin 1 => Y)
    have hslots :
        Fin.cons (X y) (fun _ : Fin 1 => Y) = vec2 (I := I) (X y) Y := by
      funext i
      fin_cases i <;> simp [vec2, DifferentialGeometry.Integral.Connection.vec2]
    rw [hslots] at h
    exact h
  · intro X Y Z
    have h := h2 X x (vec2 (I := I) Y Z)
    have hslots :
        Fin.cons (X x) (vec2 (I := I) Y Z) = vec3 (I := I) (X x) Y Z := by
      funext i
      fin_cases i
      · simp [Fin.cons_zero, vec3, DifferentialGeometry.Integral.Connection.vec3]
      · change (vec2 (I := I) Y Z) 0 = Y
        simp [vec2, DifferentialGeometry.Integral.Connection.vec2]
      · change (vec2 (I := I) Y Z) 1 = Z
        simp [vec2, DifferentialGeometry.Integral.Connection.vec2]
    rw [hslots] at h
    exact h



def Nabla2DuTrailingSymmCoord {Idx : Type*}
    (U : Idx -> Idx -> Idx -> Real) : Prop :=
  ∀ i j k : Idx, U i j k = U i k j



def OneFormRicciIdentityCoord {Idx : Type*}
    (U curvatureAction : Idx -> Idx -> Idx -> Real) : Prop :=
  ∀ i k j : Idx, U i k j - U k i j = curvatureAction i k j



def CurvatureActionTraceEqualsRicGradCoord {Idx : Type*} [Fintype Idx]
    (gInv : Idx -> Idx -> Real)
    (curvatureAction : Idx -> Idx -> Idx -> Real)
    (ricGrad : Idx -> Real) : Prop :=
  ∀ k : Idx,
    (∑ i : Idx, ∑ j : Idx, gInv i j * curvatureAction i k j) = ricGrad k




theorem oneFormRicciTraceCommCoord_of_identities {Idx : Type*} [Fintype Idx]
    (gInv : Idx -> Idx -> Real)
    (U curvatureAction : Idx -> Idx -> Idx -> Real)
    (ricGrad : Idx -> Real)
    (h_symm : Nabla2DuTrailingSymmCoord U)
    (h_comm : OneFormRicciIdentityCoord U curvatureAction)
    (h_trace : CurvatureActionTraceEqualsRicGradCoord gInv curvatureAction ricGrad) :
    ∀ k : Idx,
      (∑ i : Idx, ∑ j : Idx, gInv i j * U i j k) =
        (∑ i : Idx, ∑ j : Idx, gInv i j * U k i j) + ricGrad k := by
  intro k
  calc
    (∑ i : Idx, ∑ j : Idx, gInv i j * U i j k)
        = ∑ i : Idx, ∑ j : Idx, gInv i j * U i k j := by
          refine Finset.sum_congr rfl fun i _ => ?_
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [h_symm i j k]
    _ = ∑ i : Idx, ∑ j : Idx,
          gInv i j * (U k i j + curvatureAction i k j) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          refine Finset.sum_congr rfl fun j _ => ?_
          have h : U i k j = U k i j + curvatureAction i k j := by
            calc
              U i k j = (U i k j - U k i j) + U k i j := by ring
              _ = curvatureAction i k j + U k i j := by rw [h_comm i k j]
              _ = U k i j + curvatureAction i k j := by ring
          rw [h]
    _ = (∑ i : Idx, ∑ j : Idx, gInv i j * U k i j) +
        (∑ i : Idx, ∑ j : Idx, gInv i j * curvatureAction i k j) := by
          simp_rw [mul_add]
          simp_rw [Finset.sum_add_distrib]
    _ = (∑ i : Idx, ∑ j : Idx, gInv i j * U k i j) + ricGrad k := by
          rw [h_trace k]







def OneFormThirdCovDerivCommAt
    (Rm13 : Tensor13Section (I := I) (M := M))
    {x : M}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x) :
    Prop :=
  ∀ X Y Z : TangentSpace I x,
    nabla2Alpha (vec3 X Y Z) - nabla2Alpha (vec3 Y X Z) =
      -Rm13 x alpha (vec3 X Y Z)

theorem one_form_third_covDeriv_comm
    (Rm13 : Tensor13Section (I := I) (M := M))
    {x : M}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (h : OneFormThirdCovDerivCommAt (I := I) Rm13 alpha nabla2Alpha)
    (X Y Z : TangentSpace I x) :
    nabla2Alpha (vec3 X Y Z) - nabla2Alpha (vec3 Y X Z) =
      -Rm13 x alpha (vec3 X Y Z) :=
  h X Y Z


def swapFirstTwo0S {x : M}
    (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x :=
  A.domDomCongr (Equiv.swap (0 : Fin 3) 1)

omit [FiniteDimensional ℝ E] in
@[simp] theorem swapFirstTwo0S_apply_vec3 {x : M}
    (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (X Y Z : TangentSpace I x) :
    swapFirstTwo0S (I := I) A (vec3 X Y Z) = A (vec3 Y X Z) := by
  change A (fun i => (vec3 X Y Z) ((Equiv.swap (0 : Fin 3) 1) i)) =
    A (vec3 Y X Z)
  congr 1
  funext q
  fin_cases q <;> simp [Equiv.swap_apply_def, vec3, DifferentialGeometry.Integral.Connection.vec3]



theorem one_form_third_comm_of_coord
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (Rm13 : Tensor13Section (I := I) (M := M))
    {x : M}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (hcoord : ∀ slots : Fin 3 -> Idx,
      nabla2Alpha (fun a => basis (slots a)) -
        nabla2Alpha (fun a => basis (slots ((Equiv.swap (0 : Fin 3) 1) a))) =
          -Rm13 x alpha (fun a => basis (slots a))) :
    OneFormThirdCovDerivCommAt (I := I) Rm13 alpha nabla2Alpha := by
  have htensor :
      nabla2Alpha - swapFirstTwo0S (I := I) nabla2Alpha = -Rm13 x alpha := by
    apply ext0S_basis (I := I) basis
    intro slots
    simpa [component0S, swapFirstTwo0S] using hcoord slots
  intro X Y Z
  have h_eval := congrArg
    (fun A :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x =>
        A (vec3 X Y Z)) htensor
  change nabla2Alpha (vec3 X Y Z) -
      swapFirstTwo0S (I := I) nabla2Alpha (vec3 X Y Z) =
    -(Rm13 x alpha (vec3 X Y Z)) at h_eval
  rw [swapFirstTwo0S_apply_vec3] at h_eval
  exact h_eval


theorem one_form_third_comm_of_coord_ijk
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (Rm13 : Tensor13Section (I := I) (M := M))
    {x : M}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (hcoord : ∀ i k j : Idx,
      nabla2Alpha (vec3 (basis i) (basis k) (basis j)) -
        nabla2Alpha (vec3 (basis k) (basis i) (basis j)) =
          -Rm13 x alpha (vec3 (basis i) (basis k) (basis j))) :
    OneFormThirdCovDerivCommAt (I := I) Rm13 alpha nabla2Alpha :=
  one_form_third_comm_of_coord (I := I) Rm13 alpha basis nabla2Alpha fun slots => by
    have h := hcoord (slots 0) (slots 1) (slots 2)
    have hslots :
        (fun a => basis (slots a)) =
          vec3 (basis (slots 0)) (basis (slots 1)) (basis (slots 2)) := by
      funext q
      fin_cases q <;> simp [vec3, DifferentialGeometry.Integral.Connection.vec3]
    have hswap :
        (fun a => basis (slots ((Equiv.swap (0 : Fin 3) 1) a))) =
          vec3 (basis (slots 1)) (basis (slots 0)) (basis (slots 2)) := by
      funext q
      fin_cases q <;> simp [Equiv.swap_apply_def, vec3, DifferentialGeometry.Integral.Connection.vec3]
    simpa [hslots, hswap] using h




def OneFormLastTwoSymmAt {x : M}
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x) :
    Prop :=
  ∀ X Y Z : TangentSpace I x,
    nabla2Alpha (vec3 X Y Z) = nabla2Alpha (vec3 X Z Y)

omit [FiniteDimensional ℝ E] in
theorem one_form_last_two_symm {x : M}
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (h : OneFormLastTwoSymmAt (I := I) nabla2Alpha)
    (X Y Z : TangentSpace I x) :
    nabla2Alpha (vec3 X Y Z) = nabla2Alpha (vec3 X Z Y) :=
  h X Y Z




def traceNablaOneFormAt
    {Idx : Type*} [Fintype Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (Y : TangentSpace I x) : Real :=
  ∑ i : Idx, ∑ j : Idx,
    gInv i j * nabla2Alpha (vec3 Y (basis i) (basis j))



def OneFormRicciTraceCommWithVectorAt
    {Idx : Type*} [Fintype Idx]
    (Ric : Tensor02Section (I := I) (M := M))
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (curvatureVector : TangentSpace I x)
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x) :
    Prop :=
  ∀ Y : TangentSpace I x,
    roughLap1FormAt (I := I) basis gInv nabla2Alpha Y =
      traceNablaOneFormAt (I := I) basis gInv nabla2Alpha Y +
        Ric x (vec2 Y curvatureVector)



def nabla2OneFormCoord
    {Idx : Type*}
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (i j k : Idx) : Real :=
  nabla2Alpha (vec3 (basis i) (basis j) (basis k))




def curvatureActionOnOneFormCoord
    {Idx : Type*}
    (Rm13 : Tensor13Section (I := I) (M := M))
    {x : M}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (i k j : Idx) : Real :=
  -Rm13 x alpha (vec3 (basis i) (basis k) (basis j))


def ricciVectorCoord
    {Idx : Type*}
    (Ric : Tensor02Section (I := I) (M := M))
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (curvatureVector : TangentSpace I x)
    (k : Idx) : Real :=
  Ric x (vec2 (basis k) curvatureVector)

omit [FiniteDimensional ℝ E] in
theorem nabla2OneFormTrailingSymmCoord_of_tensor
    {Idx : Type*}
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (hsymm : OneFormLastTwoSymmAt (I := I) nabla2Alpha) :
    Nabla2DuTrailingSymmCoord
      (nabla2OneFormCoord (I := I) basis nabla2Alpha) := by
  intro i j k
  exact hsymm (basis i) (basis j) (basis k)

theorem oneFormRicciIdentityCoord_of_tensor
    {Idx : Type*}
    (Rm13 : Tensor13Section (I := I) (M := M))
    {x : M}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (hcomm : OneFormThirdCovDerivCommAt (I := I) Rm13 alpha nabla2Alpha) :
    OneFormRicciIdentityCoord
      (nabla2OneFormCoord (I := I) basis nabla2Alpha)
      (curvatureActionOnOneFormCoord (I := I) Rm13 alpha basis) := by
  intro i k j
  exact hcomm (basis i) (basis k) (basis j)



theorem oneFormRicciTraceComm_basisCoord_of_identities
    {Idx : Type*} [Fintype Idx]
    (Ric : Tensor02Section (I := I) (M := M))
    (Rm13 : Tensor13Section (I := I) (M := M))
    {x : M}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (curvatureVector : TangentSpace I x)
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (h_symm : Nabla2DuTrailingSymmCoord
      (nabla2OneFormCoord (I := I) basis nabla2Alpha))
    (h_comm : OneFormRicciIdentityCoord
      (nabla2OneFormCoord (I := I) basis nabla2Alpha)
      (curvatureActionOnOneFormCoord (I := I) Rm13 alpha basis))
    (h_trace : CurvatureActionTraceEqualsRicGradCoord gInv
      (curvatureActionOnOneFormCoord (I := I) Rm13 alpha basis)
      (ricciVectorCoord (I := I) Ric basis curvatureVector)) :
    ∀ k : Idx,
      (∑ i : Idx, ∑ j : Idx,
        gInv i j * nabla2OneFormCoord (I := I) basis nabla2Alpha i j k) =
        (∑ i : Idx, ∑ j : Idx,
          gInv i j * nabla2OneFormCoord (I := I) basis nabla2Alpha k i j) +
          ricciVectorCoord (I := I) Ric basis curvatureVector k :=
  oneFormRicciTraceCommCoord_of_identities gInv
    (nabla2OneFormCoord (I := I) basis nabla2Alpha)
    (curvatureActionOnOneFormCoord (I := I) Rm13 alpha basis)
    (ricciVectorCoord (I := I) Ric basis curvatureVector)
    h_symm h_comm h_trace

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem metricTraceInput_one_eq_vec3 {x : M}
    (X Y Z : TangentSpace I x) :
    metricTraceInput (I := I) X Y (fun _ : Fin 1 => Z) = vec3 X Y Z := by
  funext q
  fin_cases q
  · simp [metricTraceInput, vec3, DifferentialGeometry.Integral.Connection.vec3]
  · change
      Fin.cases X (fun i : Fin 2 => Fin.cases Y (fun _ : Fin 1 => Z) i)
          (Fin.succ 0) = Y
    rw [Fin.cases_succ, Fin.cases_zero]
  · change
      Fin.cases X (fun i : Fin 2 => Fin.cases Y (fun _ : Fin 1 => Z) i)
          (Fin.succ (Fin.succ 0)) = Z
    rw [Fin.cases_succ, Fin.cases_succ]





theorem oneForm_ricci_trace_comm_of_third_comm
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (Ric : Tensor02Section (I := I) (M := M))
    (Rm13 : Tensor13Section (I := I) (M := M))
    {x : M}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (curvatureVector : TangentSpace I x)
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (hsymm : OneFormLastTwoSymmAt (I := I) nabla2Alpha)
    (hcomm : OneFormThirdCovDerivCommAt (I := I) Rm13 alpha nabla2Alpha)
    (hcurv : ∀ Y : TangentSpace I x,
      -∑ i : Idx, ∑ j : Idx,
        gInv i j * Rm13 x alpha (vec3 (basis i) Y (basis j)) =
          Ric x (vec2 Y curvatureVector)) :
    OneFormRicciTraceCommWithVectorAt (I := I) Ric basis gInv curvatureVector
      nabla2Alpha := by
  intro Y
  unfold roughLap1FormAt roughLap0SAt metricTrace0S2InBasis
    traceNablaOneFormAt
  calc
    (∑ i : Idx, ∑ j : Idx,
        gInv i j *
          nabla2Alpha (metricTraceInput (I := I) (basis i) (basis j)
            (fun _ : Fin 1 => Y)))
        = ∑ i : Idx, ∑ j : Idx,
            gInv i j * nabla2Alpha (vec3 (basis i) (basis j) Y) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [metricTraceInput_one_eq_vec3]
    _ = ∑ i : Idx, ∑ j : Idx,
          gInv i j * nabla2Alpha (vec3 (basis i) Y (basis j)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hsymm (basis i) (basis j) Y]
    _ = ∑ i : Idx, ∑ j : Idx,
          gInv i j *
            (nabla2Alpha (vec3 Y (basis i) (basis j)) -
              Rm13 x alpha (vec3 (basis i) Y (basis j))) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          refine Finset.sum_congr rfl fun j _ => ?_
          congr 1
          have h := hcomm (basis i) Y (basis j)
          calc
            nabla2Alpha (vec3 (basis i) Y (basis j))
                = (nabla2Alpha (vec3 (basis i) Y (basis j)) -
                    nabla2Alpha (vec3 Y (basis i) (basis j))) +
                    nabla2Alpha (vec3 Y (basis i) (basis j)) := by ring
            _ = -Rm13 x alpha (vec3 (basis i) Y (basis j)) +
                  nabla2Alpha (vec3 Y (basis i) (basis j)) := by rw [h]
            _ = nabla2Alpha (vec3 Y (basis i) (basis j)) -
                  Rm13 x alpha (vec3 (basis i) Y (basis j)) := by ring_nf
    _ = (∑ i : Idx, ∑ j : Idx,
          gInv i j * nabla2Alpha (vec3 Y (basis i) (basis j))) +
        (-∑ i : Idx, ∑ j : Idx,
          gInv i j * Rm13 x alpha (vec3 (basis i) Y (basis j))) := by
          simp_rw [mul_sub]
          simp_rw [Finset.sum_sub_distrib]
          ring
    _ = (∑ i : Idx, ∑ j : Idx,
          gInv i j * nabla2Alpha (vec3 Y (basis i) (basis j))) +
        Ric x (vec2 Y curvatureVector) := by
          rw [hcurv Y]



def RicciIdentityOneFormAt
    (Ric : Tensor02Section (I := I) (M := M))
    {x : M}
    (roughAlpha dLapAlpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (curvatureVector : TangentSpace I x) : Prop :=
  ∀ Y : TangentSpace I x,
    roughAlpha (fun _ : Fin 1 => Y) =
      dLapAlpha (fun _ : Fin 1 => Y) + Ric x (vec2 Y curvatureVector)

theorem ricci_identity_one_form
    (Ric : Tensor02Section (I := I) (M := M))
    {x : M}
    (roughAlpha dLapAlpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (curvatureVector : TangentSpace I x)
    (h : RicciIdentityOneFormAt (I := I) Ric roughAlpha dLapAlpha curvatureVector)
    (Y : TangentSpace I x) :
    roughAlpha (fun _ : Fin 1 => Y) =
      dLapAlpha (fun _ : Fin 1 => Y) + Ric x (vec2 Y curvatureVector) :=
  h Y

theorem tensor0S_ricciIdentity_one_of_oneForm
    (Rm13 : Tensor13Section (I := I) (M := M))
    {x : M}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (h : OneFormThirdCovDerivCommAt (I := I) Rm13 alpha nabla2Alpha) :
    Tensor0SRicciIdentityAt (I := I) Rm13 alpha nabla2Alpha := by
  intro X Y slots
  have hslots : slots = fun _ : Fin 1 => slots 0 := by
    funext q
    fin_cases q
    rfl
  have hcomm := h X Y (slots 0)
  rw [hslots]
  rw [metricTraceInput_one_eq_vec3, metricTraceInput_one_eq_vec3]
  simp [curvatureAction0SAt, hcomm]

theorem oneFormThirdCovDerivCommAt_of_tensor0S_ricciIdentity_one
    (Rm13 : Tensor13Section (I := I) (M := M))
    {x : M}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (h : Tensor0SRicciIdentityAt (I := I) Rm13 alpha nabla2Alpha) :
    OneFormThirdCovDerivCommAt (I := I) Rm13 alpha nabla2Alpha := by
  intro X Y Z
  have h0 := h X Y (fun _ : Fin 1 => Z)
  simpa [Tensor0SRicciIdentityAt, curvatureAction0SAt,
    metricTraceInput_one_eq_vec3] using h0

theorem tensor0S_ricciIdentity_one
    (Rm13 : Tensor13Section (I := I) (M := M))
    {x : M}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x) :
    Tensor0SRicciIdentityAt (I := I) Rm13 alpha nabla2Alpha ↔
      OneFormThirdCovDerivCommAt (I := I) Rm13 alpha nabla2Alpha :=
  ⟨oneFormThirdCovDerivCommAt_of_tensor0S_ricciIdentity_one (I := I)
      Rm13 alpha nabla2Alpha,
    tensor0S_ricciIdentity_one_of_oneForm (I := I) Rm13 alpha nabla2Alpha⟩


end DifferentialGeometry.Integral.Connection
