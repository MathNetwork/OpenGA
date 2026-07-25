import DifferentialGeometry.Geometry.Curvature.Bochner.ScalarBochner
import DifferentialGeometry.Geometry.Connection.LeviCivita.Smooth.Connection
import DifferentialGeometry.Geometry.Connection.LeviCivita.Torsion
import DifferentialGeometry.Geometry.Coordinates.NablaComponents.OneForm.Basic
import DifferentialGeometry.Geometry.Coordinates.NablaComponents.OneForm.Pairing
import DifferentialGeometry.Geometry.Coordinates.NablaComponents.OneForm.ConnectionProduct
import DifferentialGeometry.Geometry.Coordinates.NablaComponents.OneForm.Moving
import DifferentialGeometry.Geometry.Coordinates.NablaComponents.OneForm.Smoothness
import DifferentialGeometry.Geometry.Coordinates.NablaComponents.TwoTensor

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false










noncomputable section

namespace DifferentialGeometry.Integral.Connection

open Bundle Tensor0SBundle
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Tensor.Coordinates
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M]


omit [CompleteSpace E] [IsManifold I 3 M] in
private theorem nabla0SFun_one_eval_smooth_slots
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X Y : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (α : OneFormSection (I := I) (M := M)) (x : M) :
    (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      1 cov X α x) (fun _ : Fin 1 => Y x) =
      extDerivFun (I := I) (fun p : M => α p (fun _ : Fin 1 => Y p)) x (X x) -
        α x (fun _ : Fin 1 => (cov (fun p : M => Y p) x) (X x)) := by
  classical
  let V : Fin 1 -> (p : M) -> TangentSpace I p := fun _ p => Y p
  let Ysec : Fin 1 -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _) := fun _ => Y
  have hpair : MDifferentiableAt I 𝓘(Real, Real)
      (fun p : M => α p (fun a : Fin 1 => V a p)) x := by
    have hEval := TensorMultilinear.contMDiff_tensor0SField_apply
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (n := 1)
      α Ysec
    exact (by
      simpa [V, Ysec] using hEval.contMDiffAt.mdifferentiableAt (by simp))
  have hV : ∀ a : Fin 1, MDiffAt (T% (V a)) x := by
    intro a
    exact Y.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hVmodel : ∀ a : Fin 1,
      DifferentiableWithinAt Real
        (TensorLieDeriv.tangentFieldModelInChart (𝕜 := Real) (I := I) x (V a))
        (Set.range I) (extChartAt I x x) := by
    intro a
    exact
      tangentFieldModelInChart_differentiableWithinAt_center_of_contMDiffAt
        (I := I) (V a) x Y.contMDiff.contMDiffAt
  have hcoord : ∀ a : Fin 1, ∀ i : Fin (Module.finrank Real E),
      MDifferentiableAt I 𝓘(Real, Real)
        (fun p : M =>
          (Module.finBasis Real E).coord i
            (TensorLieDeriv.tangentFieldModelInChart (𝕜 := Real) (I := I) x (V a)
              (extChartAt I x p))) x := by
    intro a i
    exact
      tangentFieldModelInChart_coord_mdiffAt_center_of_contMDiffAt
        (I := I) (V a) x Y.contMDiff.contMDiffAt i
  have h := Tensor0SBundle.nabla0SFun_eval_coordFrame_moving_raw
    (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    (s := 1) cov X V α x hpair hV hVmodel hcoord
  have hupdate (w : TangentSpace I x) :
      Function.update (fun _ : Fin 1 => Y x) (0 : Fin 1) w =
        fun _ : Fin 1 => w := by
    funext q
    fin_cases q
    simp
  simpa [V, hupdate] using h


private theorem leviCivita_nablaDuSec_pointwise_symm_direct
    [SigmaCompactSpace M] [T2Space M]
    (g : SmoothRiemannianMetric I M) (u : M -> Real)
    (hu : ContMDiff I 𝓘(Real, Real) ∞ u)
    (duSec : OneFormSection (I := I) (M := M))
    (nablaDuSec : TwoTensorSection (I := I) (M := M))
    (hnabla : NablaOneFormSectionRealizes (I := I)
      (leviCivitaConnectionOfMetric (I := I) g) duSec nablaDuSec)
    (hdu : DuFieldRealizes (I := I) u duSec)
    (x : M) (U V : TangentSpace I x) :
    nablaDuSec x (vec2 (I := I) U V) =
      nablaDuSec x (vec2 (I := I) V U) := by
  classical
  let cov := leviCivitaConnectionOfMetric (I := I) g
  obtain ⟨X, hXx⟩ :=
    ContMDiffSection.exists_eq_at_gen
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x U
  obtain ⟨Y, hYx⟩ :=
    ContMDiffSection.exists_eq_at_gen
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x V
  have hXmd : MDiffAt (T% (fun p : M => X p)) x :=
    X.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hYmd : MDiffAt (T% (fun p : M => Y p)) x :=
    Y.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hX2 :
      ContMDiffAt I (I.prod 𝓘(Real, E)) (minSmoothness Real 2)
        (T% (fun p : M => X p)) x := by
    exact X.contMDiff.contMDiffAt.of_le (by
      rw [minSmoothness_of_isRCLikeNormedField]
      exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ (⊤ : ℕ∞)))
  have hY2 :
      ContMDiffAt I (I.prod 𝓘(Real, E)) (minSmoothness Real 2)
        (T% (fun p : M => Y p)) x := by
    exact Y.contMDiff.contMDiffAt.of_le (by
      rw [minSmoothness_of_isRCLikeNormedField]
      exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ (⊤ : ℕ∞)))
  have hu2 : ContMDiffAt I 𝓘(Real, Real) (minSmoothness Real 2) u x := by
    exact hu.contMDiffAt.of_le (by
      rw [minSmoothness_of_isRCLikeNormedField]
      exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ (⊤ : ℕ∞)))
  let covYX : TangentSpace I x := (cov (fun p : M => Y p) x) (X x)
  let covXY : TangentSpace I x := (cov (fun p : M => X p) x) (Y x)
  let bracket : TangentSpace I x :=
    VectorField.mlieBracket I (fun p : M => X p) (fun p : M => Y p) x
  have hleft :
      nablaDuSec x (vec2 (I := I) U V) =
        nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          1 cov X duSec x (fun _ : Fin 1 => Y x) := by
    simpa [cov, hXx, hYx] using hnabla x X V
  have hright :
      nablaDuSec x (vec2 (I := I) V U) =
        nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          1 cov Y duSec x (fun _ : Fin 1 => X x) := by
    simpa [cov, hXx, hYx] using hnabla x Y U
  have hleft_eval :
      nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        1 cov X duSec x (fun _ : Fin 1 => Y x) =
        extDerivFun (I := I) (fun p : M => duSec p (fun _ : Fin 1 => Y p)) x (X x) -
          duSec x (fun _ : Fin 1 => covYX) := by
    simpa [cov, covYX] using
      nabla0SFun_one_eval_smooth_slots (I := I) cov X Y duSec x
  have hright_eval :
      nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        1 cov Y duSec x (fun _ : Fin 1 => X x) =
        extDerivFun (I := I) (fun p : M => duSec p (fun _ : Fin 1 => X p)) x (Y x) -
          duSec x (fun _ : Fin 1 => covXY) := by
    simpa [cov, covXY] using
      nabla0SFun_one_eval_smooth_slots (I := I) cov Y X duSec x
  have hduY_fun :
      (fun p : M => duSec p (fun _ : Fin 1 => Y p)) =
        fun p : M => extDerivFun (I := I) u p (Y p) := by
    funext p
    rw [hdu p]
    simp [duField, differential1FormFun_apply_eq_extDerivFun]
  have hduX_fun :
      (fun p : M => duSec p (fun _ : Fin 1 => X p)) =
        fun p : M => extDerivFun (I := I) u p (X p) := by
    funext p
    rw [hdu p]
    simp [duField, differential1FormFun_apply_eq_extDerivFun]
  have hscalar :
      extDerivFun (I := I) (fun p : M => duSec p (fun _ : Fin 1 => Y p)) x (X x) -
          extDerivFun (I := I) (fun p : M => duSec p (fun _ : Fin 1 => X p)) x (Y x) =
        extDerivFun (I := I) u x bracket := by
    rw [hduY_fun, hduX_fun]
    exact (extDerivFun_apply_mlieBracket
      (I := I) (fun p : M => X p) (fun p : M => Y p) u x hX2 hY2 hu2).symm
  have htf := leviCivitaConnectionOfMetric_isTorsionFree (I := I) g
  have htorsion :
      covYX - covXY = bracket := by
    simpa [cov, covYX, covXY, bracket] using
      torsion_free_apply (I := I) htf (x := x)
        (X := fun p : M => X p) (Y := fun p : M => Y p) hXmd hYmd
  have hcorr :
      duSec x (fun _ : Fin 1 => covYX) -
          duSec x (fun _ : Fin 1 => covXY) =
        extDerivFun (I := I) u x bracket := by
    rw [hdu x]
    simp only [duField, differential1FormFun_apply_eq_extDerivFun]
    unfold extDerivFun
    rw [← map_sub, htorsion]
  rw [hleft, hright, hleft_eval, hright_eval]
  linarith








private theorem leviCivita_nablaDuSec_coordFrame_symm
    [SigmaCompactSpace M] [T2Space M]
    (g : SmoothRiemannianMetric I M) (u : M -> Real)
    (hu : ContMDiff I 𝓘(Real, Real) ∞ u)
    (duSec : OneFormSection (I := I) (M := M))
    (nablaDuSec : TwoTensorSection (I := I) (M := M))
    (hnabla : NablaOneFormSectionRealizes (I := I)
      (leviCivitaConnectionOfMetric (I := I) g) duSec nablaDuSec)
    (hdu : DuFieldRealizes (I := I) u duSec)
    (x : M) (i j : CoordinateIdx (𝕜 := Real) E) :
    nablaDuSec x (vec2
        (coordinateFrameAt_toBasis (I := I) x i)
        (coordinateFrameAt_toBasis (I := I) x j)) =
    nablaDuSec x (vec2
        (coordinateFrameAt_toBasis (I := I) x j)
        (coordinateFrameAt_toBasis (I := I) x i)) := by
  exact leviCivita_nablaDuSec_pointwise_symm_direct
    (I := I) g u hu duSec nablaDuSec hnabla hdu x
    (coordinateFrameAt_toBasis (I := I) x i)
    (coordinateFrameAt_toBasis (I := I) x j)



private theorem leviCivita_nablaDuSec_pointwise_symm
    [SigmaCompactSpace M] [T2Space M]
    (g : SmoothRiemannianMetric I M) (u : M -> Real)
    (hu : ContMDiff I 𝓘(Real, Real) ∞ u)
    (duSec : OneFormSection (I := I) (M := M))
    (nablaDuSec : TwoTensorSection (I := I) (M := M))
    (hnabla : NablaOneFormSectionRealizes (I := I)
      (leviCivitaConnectionOfMetric (I := I) g) duSec nablaDuSec)
    (hdu : DuFieldRealizes (I := I) u duSec)
    (x : M) :
    ∀ U V : TangentSpace I x,
      nablaDuSec x (vec2 U V) = nablaDuSec x (vec2 V U) := by
  intro U V
  have hsymm := DifferentialGeometry.Tensor.Coordinates.tensor0S_two_symm_of_coordFrame
    (I := I) (coordinateFrameAt_toBasis (I := I) x) (nablaDuSec x) ?_
  · exact hsymm U V
  intro i j
  simpa [vec2] using
    leviCivita_nablaDuSec_coordFrame_symm
      (I := I) g u hu duSec nablaDuSec hnabla hdu x i j



theorem hessSymm
    [SigmaCompactSpace M] [T2Space M]
    (g : SmoothRiemannianMetric I M) (u : M -> Real)
    (hu : ContMDiff I 𝓘(Real, Real) ∞ u)
    {x : M} (U V : TangentSpace I x) :
    let cov := leviCivitaConnectionOfMetric (I := I) g
    let hcov :=
      leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
        (I := I) (M := M) g
    let Hess := hessianSec (I := I) cov hcov u hu
    Hess x (vec2 (I := I) U V) = Hess x (vec2 (I := I) V U) := by
  classical
  let cov := leviCivitaConnectionOfMetric (I := I) g
  let hcov :=
    leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
      (I := I) (M := M) g
  let du := duSec (I := I) u hu
  let Hess := hessianSec (I := I) cov hcov u hu
  have hnabla :
      NablaOneFormSectionRealizes (I := I) cov du Hess := by
    simpa [cov, hcov, du, Hess] using
      hessianSec_nabla (I := I) cov hcov u hu
  have hdu : DuFieldRealizes (I := I) u du := by
    simpa [du] using duSec_realizes (I := I) u hu
  simpa [cov, hcov, du, Hess] using
    leviCivita_nablaDuSec_pointwise_symm
      (I := I) g u hu du Hess hnabla hdu x U V



theorem oneFormLastTwoSymmAt_of_leviCivita_du
    [SigmaCompactSpace M] [T2Space M]
    (g : SmoothRiemannianMetric I M) (u : M -> Real)
    (hu : ContMDiff I 𝓘(Real, Real) ∞ u)
    (duSec : OneFormSection (I := I) (M := M))
    (nablaDuSec : TwoTensorSection (I := I) (M := M))
    {x : M}
    (nabla2Du :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (hdu : DuFieldRealizes (I := I) u duSec)
    (hnabla2 : Nabla2OneFormRealizesAt (I := I)
      (leviCivitaConnectionOfMetric (I := I) g) duSec nablaDuSec x nabla2Du) :
    OneFormLastTwoSymmAt (I := I) nabla2Du := by
  classical
  have hnabla := nabla2OneFormRealizesAt_first
    (I := I) (leviCivitaConnectionOfMetric (I := I) g)
    duSec nablaDuSec x nabla2Du hnabla2
  have hsymm : ∀ y : M, ∀ U V : TangentSpace I y,
      nablaDuSec y (vec2 (I := I) U V) =
        nablaDuSec y (vec2 (I := I) V U) :=
    fun y U V =>
      leviCivita_nablaDuSec_pointwise_symm
        (I := I) g u hu duSec nablaDuSec hnabla hdu y U V
  intro X Y Z
  let cov := leviCivitaConnectionOfMetric (I := I) g
  obtain ⟨S, hSx⟩ :=
    ContMDiffSection.exists_eq_at_gen
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x X
  have hleft := nabla2OneFormRealizesAt_apply
    (I := I) cov duSec nablaDuSec x nabla2Du hnabla2 S Y Z
  have hright := nabla2OneFormRealizesAt_apply
    (I := I) cov duSec nablaDuSec x nabla2Du hnabla2 S Z Y
  have hs :=
    DifferentialGeometry.Tensor.Coordinates.nabla0SFun_two_symm_of_symm
      (I := I) cov S nablaDuSec x hsymm Y Z
  rw [← hSx]
  rw [hleft, hright]
  simpa [vec2] using hs

end DifferentialGeometry.Integral.Connection
