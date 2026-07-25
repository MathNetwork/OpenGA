import DifferentialGeometry.Geometry.Connection.MetricCompatibility
import DifferentialGeometry.Geometry.Operator.Operators
import DifferentialGeometry.Geometry.Operator.GradientRegularity
import DifferentialGeometry.Geometry.Operator.RoughLaplacian
import DifferentialGeometry.Geometry.Coordinates.NablaComponents.OneForm.Basic
import DifferentialGeometry.Geometry.Coordinates.NablaComponents.OneForm.Pairing
import DifferentialGeometry.Geometry.Coordinates.NablaComponents.OneForm.ConnectionProduct
import DifferentialGeometry.Geometry.Coordinates.NablaComponents.OneForm.Moving
import DifferentialGeometry.Geometry.Coordinates.NablaComponents.OneForm.Smoothness
import DifferentialGeometry.Tensor.RicciIdentity.OneForm
import DifferentialGeometry.Tensor.RicciIdentity.Tensor0S.Realization
import DifferentialGeometry.Tensor.RicciIdentity.Tensor0S.Formula
import DifferentialGeometry.Tensor.RicciIdentity.MixedComponents
import DifferentialGeometry.Bundle.LocalFrameRegularity
import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.Regularity.TotalNabla0S
import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.ConnectionDifference

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option backward.isDefEq.respectTransparency false








noncomputable section

namespace DifferentialGeometry.Integral.Connection

open Bundle Tensor0SBundle
open DifferentialGeometry.Tensor.Coordinates
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]


def differential1FormFun (u : M -> Real) (x : M) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x :=
  dualToCotangent_gen (I := I) (mfderiv I 𝓘(Real, Real) u x).toLinearMap



def duField (u : M -> Real) (x : M) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x :=
  differential1FormFun (I := I) u x


def DuFieldRealizes (u : M -> Real)
    (du : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (∞ : WithTop ℕ∞) 1) : Prop :=
  ∀ x : M, du x = duField (I := I) u x

private theorem duFun_contMDiff
    (u : M -> Real) (hu : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) u) :
    letI := tensor0SBundle_topology (𝕜 := Real) (E := E) (H := H) (I := I)
      (M := M) 1
    letI := TangentBundle.contMDiffVectorBundle (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞))
    ContMDiff I (I.prod 𝓘(Real, Tensor0SModel 1 Real E)) (∞ : WithTop ℕ∞)
      (fun p : M =>
        (⟨p, differential1FormFun (I := I) u p⟩ :
          TotalSpace (Tensor0SModel 1 Real E)
            (fun p : M => Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
              (I := I) (M := M) 1 p))) := by
  letI := tensor0SBundle_topology (𝕜 := Real) (E := E) (H := H) (I := I)
    (M := M) 1
  letI := TangentBundle.contMDiffVectorBundle (I := I) (M := M)
    (n := (∞ : WithTop ℕ∞))
  let d := Module.finrank Real E
  let b : Module.Basis (Fin d) Real E := Module.finBasis Real E
  let F : (p : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 p :=
    fun p : M => differential1FormFun (I := I) u p
  refine (contMDiff_multilinearSection_iff_coord (TangentSpace I)
    (∞ : WithTop ℕ∞) b F).mpr ?_
  intro σ x₀
  let j : CoordinateIdx (𝕜 := Real) E := σ 0
  have hframe :
      ContMDiffAt I (I.prod 𝓘(Real, E)) (∞ : WithTop ℕ∞)
        (fun p : M =>
          (⟨p, coordinateFrameAt (I := I) x₀ j p⟩ :
            TotalSpace E (TangentSpace I : M -> Type _))) x₀ := by
    exact (coordinateFrameAt_isLocalFrame (I := I) x₀).contMDiffAt
      (coordinateFrameSet_open (I := I) x₀)
      (coordinateFrameAt_mem (I := I) x₀) j
  have hderiv :
      ContMDiffAt I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
        (fun p : M =>
          extDerivFun (I := I) u p (coordinateFrameAt (I := I) x₀ j p)) x₀ :=
    extDerivFun_apply_contMDiffAt_of_section (I := I)
      (f := u) (X := coordinateFrameAt (I := I) x₀ j)
      hu.contMDiffAt hframe
  refine hderiv.congr_of_eventuallyEq ?_
  filter_upwards
    [(coordinateFrameSet_open (I := I) x₀).mem_nhds
      (coordinateFrameAt_mem (I := I) x₀)] with p hp
  have hslot :
      (fun a : Fin 1 =>
          (trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL Real p
            (b (σ a))) =
        fun _ : Fin 1 => coordinateFrameAt (I := I) x₀ j p := by
    funext a
    fin_cases a
    have hp_src : p ∈ (chartAt H x₀).source := by
      simpa [coordinateFrameSet, coordinateTrivializationAt] using hp
    rw [coordinateFrameAt_apply_of_mem (I := I) (x₀ := x₀) (x := p) hp j]
    simpa [j, b] using
      congrArg
        (fun L : E →L[Real] TangentSpace I p => L (b j))
        (TangentBundle.symmL_trivializationAt (I := I) (𝕜 := Real) hp_src)
  rw [continuousMultilinearMap_basis_repr]
  change ((trivializationAt (Tensor0SModel 1 Real E)
      (Bundle.continuousMultilinearMap Real 1 E (TangentSpace I : M -> Type _)) x₀
      ⟨p, F p⟩).2)
      (fun a : Fin 1 => b (σ a)) =
    extDerivFun (I := I) u p (coordinateFrameAt (I := I) x₀ j p)
  change (F p).compContinuousLinearMap
      (fun _ : Fin 1 =>
        (trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL Real p)
      (fun a : Fin 1 => b (σ a)) =
    extDerivFun (I := I) u p (coordinateFrameAt (I := I) x₀ j p)
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply, hslot]
  simp [F, differential1FormFun, extDerivFun, NormedSpace.fromTangentSpace]
  rfl



noncomputable def duSec
    (u : M -> Real) (hu : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) u) :
    OneFormSection (I := I) (M := M) := by
  letI := tensor0SBundle_topology (𝕜 := Real) (E := E) (H := H) (I := I)
    (M := M) 1
  exact ⟨fun x : M => differential1FormFun (I := I) u x,
    duFun_contMDiff (I := I) u hu⟩

@[simp]
theorem duSec_apply
    (u : M -> Real) (hu : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) u)
    (x : M) :
    duSec (I := I) u hu x = differential1FormFun (I := I) u x := by
  rfl


theorem duSec_realizes
    (u : M -> Real) (hu : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) u) :
    DuFieldRealizes (I := I) u (duSec (I := I) u hu) := by
  intro x
  simp [duField]



theorem differential1FormFun_apply_eq_extDerivFun
    (u : M -> Real) (x : M) (v : TangentSpace I x) :
    differential1FormFun (I := I) u x (fun _ : Fin 1 => v) =
      extDerivFun (I := I) u x v := by
  simp [differential1FormFun, extDerivFun, NormedSpace.fromTangentSpace]
  rfl



theorem dphi_apply_smooth
    (u : M -> Real) (hu : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) u)
    (Y : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _)) :
    ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
      (fun p : M => extDerivFun (I := I) u p (Y p)) := by
  let du : OneFormSection (I := I) (M := M) := duSec (I := I) u hu
  let Slots : Fin 1 ->
      ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
    fun _ => Y
  have hraw :=
    TensorMultilinear.contMDiff_tensor0SField_apply (I := I) (M := M) du Slots
  have hfun :
      (fun p : M => du p (fun i : Fin 1 => Slots i p)) =
        fun p : M => extDerivFun (I := I) u p (Y p) := by
    funext p
    rw [duSec_apply]
    exact differential1FormFun_apply_eq_extDerivFun (I := I) u p (Y p)
  simpa [hfun] using hraw



theorem dphi_apply_mdiffAt
    (u : M -> Real) (hu : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) u)
    (Y : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (x : M) :
    MDifferentiableAt I 𝓘(Real, Real)
      (fun p : M => extDerivFun (I := I) u p (Y p)) x :=
  (dphi_apply_smooth (I := I) u hu Y).contMDiffAt.mdifferentiableAt (by simp)


theorem differential1FormFun_apply_eq_inner_gradientFun
    (g : SmoothRiemannianMetric I M) (u : M -> Real)
    (x : M) (v : TangentSpace I x) :
    differential1FormFun (I := I) u x (fun _ : Fin 1 => v) =
      g.inner x (gradientFun (I := I) g u x) v := by
  simpa [differential1FormFun] using
    (inner_gradientFun (I := I) g u x v).symm

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
private theorem extDerivFun_real_eq_mfderiv
    (u : M -> Real) (x : M) (v : TangentSpace I x) :
    extDerivFun (I := I) u x v =
      mfderiv I 𝓘(Real, Real) u x v := by
  simp [extDerivFun, NormedSpace.fromTangentSpace]




noncomputable def nablaDuAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (du : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (∞ : WithTop ℕ∞) 1) (x : M) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x :=
  nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 cov X du x



def hessianAt
    (Hess : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (x : M) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x :=
  Hess x



def HessianRealizesNablaDuAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (du : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (∞ : WithTop ℕ∞) 1)
    (Hess : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (x : M) : Prop :=
  ∀ (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
      (Y : TangentSpace I x),
    Hess x (vec2 (X x) Y) =
      nablaDuAt (I := I) cov X du x (fun _ : Fin 1 => Y)

theorem nablaDu_eq_hessian
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (du : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (∞ : WithTop ℕ∞) 1)
    (Hess : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (x : M)
    (hHess : HessianRealizesNablaDuAt (I := I) cov du Hess x)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (Y : TangentSpace I x) :
    nablaDuAt (I := I) cov X du x (fun _ : Fin 1 => Y) =
      Hess x (vec2 (X x) Y) :=
  (hHess X Y).symm



theorem hess_of_nabla
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (du : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (∞ : WithTop ℕ∞) 1)
    (Hess : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (x : M)
    (h : NablaOneFormRealizesAt (I := I) cov du Hess x) :
    HessianRealizesNablaDuAt (I := I) cov du Hess x := by
  intro X Y
  simpa [nablaDuAt] using h X Y



noncomputable def hessianSec
    [T2Space M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (u : M -> Real) (hu : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) u) :
    TwoTensorSection (I := I) (M := M) :=
  totalNabla0S (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    1 cov (duSec (I := I) u hu)
    (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
      1 cov hcov (duSec (I := I) u hu))

@[simp]
theorem hessianSec_apply
    [T2Space M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (u : M -> Real) (hu : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) u)
    (x : M) :
    hessianSec (I := I) cov hcov u hu x =
      totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        1 cov (duSec (I := I) u hu) x := by
  rfl



theorem hessianSec_nabla
    [T2Space M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (u : M -> Real) (hu : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) u) :
    NablaOneFormSectionRealizes (I := I) cov (duSec (I := I) u hu)
      (hessianSec (I := I) cov hcov u hu) := by
  intro x X Y
  have hreal :=
    totalNabla0S_realizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      1 cov (duSec (I := I) u hu)
      (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
        1 cov hcov (duSec (I := I) u hu))
  have h := TotalNabla0SRealizes.apply (I := I) hreal X x (fun _ : Fin 1 => Y)
  have hslots :
      Fin.cons (X x) (fun _ : Fin 1 => Y) = vec2 (I := I) (X x) Y := by
    funext a
    fin_cases a <;> rfl
  rw [← hslots]
  simpa [hessianSec, nablaDuAt] using h



theorem hess_sub_conn
    [T2Space M]
    (cov cov' : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (hcov' : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov'
      (∞ : WithTop ℕ∞))
    (u : M -> Real) (hu : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) u)
    (x : M) :
    hessianSec (I := I) cov hcov u hu x -
        hessianSec (I := I) cov' hcov' u hu x =
      -connectionDifferenceOutput (I := I)
        (CovariantDerivative.difference cov cov' x) (duSec (I := I) u hu x) := by
  classical
  let basis : Module.Basis (Fin (Module.finrank Real (TangentSpace I x))) Real
      (TangentSpace I x) :=
    Module.finBasis Real (TangentSpace I x)
  apply ext0S_basis (I := I) basis
  intro slots
  let X : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _) :=
    (ContMDiffSection.exists_eq_at_gen
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
      x (basis (slots 0))).choose
  let Y : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _) :=
    (ContMDiffSection.exists_eq_at_gen
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
      x (basis (slots 1))).choose
  have hX : X x = basis (slots 0) :=
    (ContMDiffSection.exists_eq_at_gen
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
      x (basis (slots 0))).choose_spec
  have hY : Y x = basis (slots 1) :=
    (ContMDiffSection.exists_eq_at_gen
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
      x (basis (slots 1))).choose_spec
  have hslots :
      (fun a : Fin 2 => basis (slots a)) = vec2 (I := I) (X x) (Y x) := by
    funext a
    fin_cases a <;> simp [vec2, hX, hY]
  have hdiff :=
    nabla0SFun_sub_cov (I := I) cov cov' X (fun _ : Fin 1 => Y)
      (duSec (I := I) u hu) x
  simp only [component0S_apply]
  rw [hslots]
  change
    hessianSec (I := I) cov hcov u hu x (vec2 (I := I) (X x) (Y x)) -
        hessianSec (I := I) cov' hcov' u hu x (vec2 (I := I) (X x) (Y x)) =
      -(connectionDifferenceOutput (I := I)
        (CovariantDerivative.difference cov cov' x) (duSec (I := I) u hu x)
          (vec2 (I := I) (X x) (Y x)))
  rw [(hessianSec_nabla (I := I) cov hcov u hu) x X (Y x),
    (hessianSec_nabla (I := I) cov' hcov' u hu) x X (Y x)]
  rw [connectionDifferenceOutput_apply]
  simpa [vec2] using hdiff


theorem hessianSec_realizesAt
    [T2Space M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (u : M -> Real) (hu : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) u)
    (x : M) :
    HessianRealizesNablaDuAt (I := I) cov (duSec (I := I) u hu)
      (fun y : M => hessianSec (I := I) cov hcov u hu y) x :=
  hess_of_nabla (I := I) cov (duSec (I := I) u hu)
    (fun y : M => hessianSec (I := I) cov hcov u hu y) x
    ((hessianSec_nabla (I := I) cov hcov u hu) x)



theorem hessSec_inner_cov
    [T2Space M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (g : SmoothRiemannianMetric I M)
    (hmc : DifferentialGeometry.Integral.Connection.IsMetricCompatible_gen
      (I := I) cov g)
    (f : M -> Real) (hf : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) f)
    (x : M) (v w : TangentSpace I x) :
    hessianSec (I := I) cov hcov f hf x (vec2 (I := I) v w) =
      g.inner x ((cov (fun y : M => gradientFun (I := I) g f y) x) v) w := by
  let X : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _) :=
    (ContMDiffSection.exists_eq_at_gen
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x v).choose
  let Y : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _) :=
    (ContMDiffSection.exists_eq_at_gen
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x w).choose
  let G : (y : M) -> TangentSpace I y :=
    fun y => gradientFun (I := I) g f y
  have hX : X x = v :=
    (ContMDiffSection.exists_eq_at_gen
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x v).choose_spec
  have hY : Y x = w :=
    (ContMDiffSection.exists_eq_at_gen
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x w).choose_spec
  have hXm : MDiffAt (T% fun y : M => X y) x :=
    X.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hYm : MDiffAt (T% fun y : M => Y y) x :=
    Y.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hGm : MDiffAt (T% fun y : M => G y) x :=
    gradientFun_mdiffAt (I := I) g hf x
  have hmetric := DifferentialGeometry.Integral.Connection.metric_compatible_apply
    (I := I) hmc (fun y : M => X y) G (fun y : M => Y y) hXm hGm hYm
  have hmetric_ext :
      extDerivFun (I := I) (fun y : M => g.inner y (G y) (Y y)) x (X x) =
        g.inner x (cov G x (X x)) (Y x) +
          g.inner x (G x) (cov (fun y : M => Y y) x (X x)) := by
    rw [extDerivFun_real_eq_mfderiv]
    exact hmetric
  have hnabla_eval :
      nablaDuAt (I := I) cov X (duSec (I := I) f hf) x
          (fun _ : Fin 1 => Y x) =
        extDerivFun (I := I)
            (fun y : M => duSec (I := I) f hf y (fun _ : Fin 1 => Y y)) x
            (X x) -
          duSec (I := I) f hf x
            (fun _ : Fin 1 => (cov (fun y : M => Y y) x) (X x)) := by
    simpa [nablaDuAt] using
      nabla0SFun_one_eval_smooth_slots (I := I) cov X Y
        (duSec (I := I) f hf) x
  have hdu :
      (fun y : M => duSec (I := I) f hf y (fun _ : Fin 1 => Y y)) =
        fun y : M => g.inner y (G y) (Y y) := by
    funext y
    rw [duSec_apply]
    exact differential1FormFun_apply_eq_inner_gradientFun (I := I) g f y (Y y)
  have hcorr :
      duSec (I := I) f hf x
          (fun _ : Fin 1 => (cov (fun y : M => Y y) x) (X x)) =
        g.inner x (G x) (cov (fun y : M => Y y) x (X x)) := by
    rw [duSec_apply]
    exact differential1FormFun_apply_eq_inner_gradientFun
      (I := I) g f x ((cov (fun y : M => Y y) x) (X x))
  calc
    hessianSec (I := I) cov hcov f hf x (vec2 (I := I) v w) =
        hessianSec (I := I) cov hcov f hf x
          (vec2 (I := I) (X x) (Y x)) := by rw [hX, hY]
    _ = nablaDuAt (I := I) cov X (duSec (I := I) f hf) x
          (fun _ : Fin 1 => Y x) :=
      (hessianSec_nabla (I := I) cov hcov f hf) x X (Y x)
    _ = extDerivFun (I := I)
          (fun y : M => duSec (I := I) f hf y (fun _ : Fin 1 => Y y)) x
          (X x) -
        duSec (I := I) f hf x
          (fun _ : Fin 1 => (cov (fun y : M => Y y) x) (X x)) := hnabla_eval
    _ = extDerivFun (I := I) (fun y : M => g.inner y (G y) (Y y)) x (X x) -
        g.inner x (G x) (cov (fun y : M => Y y) x (X x)) := by
      rw [hdu, hcorr]
    _ = g.inner x (cov G x (X x)) (Y x) := by
      rw [hmetric_ext]
      ring
    _ = g.inner x ((cov (fun y : M => gradientFun (I := I) g f y) x) v) w := by
      rw [hX, hY]



noncomputable def nablaHessSec
    [T2Space M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (u : M -> Real) (hu : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) u) :
    Tensor0SSection (I := I) (M := M) 3 :=
  totalNabla0S (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    2 cov (hessianSec (I := I) cov hcov u hu)
    (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
      2 cov hcov (hessianSec (I := I) cov hcov u hu))

@[simp]
theorem nablaHess_apply
    [T2Space M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (u : M -> Real) (hu : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) u)
    (x : M) :
    nablaHessSec (I := I) cov hcov u hu x =
      totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 cov (hessianSec (I := I) cov hcov u hu) x := by
  rfl



theorem nablaHess_realizes
    [T2Space M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (u : M -> Real) (hu : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) u)
    (x : M) :
    Nabla2OneFormRealizesAt (I := I) cov (duSec (I := I) u hu)
      (hessianSec (I := I) cov hcov u hu) x
      (nablaHessSec (I := I) cov hcov u hu x) := by
  have h1 :
      TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        1 cov (duSec (I := I) u hu)
        (hessianSec (I := I) cov hcov u hu) := by
    simpa [hessianSec] using
      (totalNabla0S_realizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        1 cov (duSec (I := I) u hu)
        (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
          1 cov hcov (duSec (I := I) u hu)))
  have h2 :
      TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 cov (hessianSec (I := I) cov hcov u hu)
        (nablaHessSec (I := I) cov hcov u hu) := by
    simpa [nablaHessSec] using
      (totalNabla0S_realizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 cov (hessianSec (I := I) cov hcov u hu)
        (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
          2 cov hcov (hessianSec (I := I) cov hcov u hu)))
  exact nabla2OneFormRealizesAt_of_totalNabla (I := I) cov
    (duSec (I := I) u hu) (hessianSec (I := I) cov hcov u hu)
    (nablaHessSec (I := I) cov hcov u hu) h1 h2 x



theorem freezeFirst_elim0 {x : M}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :
    freezeFirstTwo0S (I := I) T Fin.elim0 = T := by
  classical
  let basis : Module.Basis (Fin (Module.finrank Real (TangentSpace I x))) Real
      (TangentSpace I x) :=
    Module.finBasis Real (TangentSpace I x)
  apply ext0S_basis (I := I) basis
  intro slots
  have hslots :
      (fun a : Fin 2 => basis (slots a)) =
        vec2 (I := I) (basis (slots 0)) (basis (slots 1)) := by
    funext a
    fin_cases a <;> rfl
  simp only [component0S_apply]
  rw [hslots, freezeFirstTwo0S_apply]
  congr 1
  funext a
  fin_cases a <;> rfl


theorem traceFirstTwo_elim0
    (g : SmoothRiemannianMetric I M) {x : M}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :
    metricTraceFirstTwo0SAt (I := I) g T Fin.elim0 =
      metricTracePair0SAt (I := I) g T := by
  rw [metricTraceFirstTwo0SAt, freezeFirst_elim0]




def scalarLapTraceAt
    (g : SmoothRiemannianMetric I M)
    {x : M}
    (hessF :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :
    Real :=
  metricTracePair0SAt (I := I) g hessF

@[simp]
theorem scalarLapTraceAt_eq_pair
    (g : SmoothRiemannianMetric I M)
    {x : M}
    (hessF :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :
    scalarLapTraceAt (I := I) g hessF =
      metricTracePair0SAt (I := I) g hessF := by
  rfl

theorem scalarLapTraceAt_eq_firstTwo
    (g : SmoothRiemannianMetric I M)
    {x : M}
    (hessF :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :
    scalarLapTraceAt (I := I) g hessF =
      metricTraceFirstTwo0SAt (I := I) g hessF Fin.elim0 := by
  rw [scalarLapTraceAt, traceFirstTwo_elim0]



def ScalarLaplacianRealizesTraceAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    {x : M}
    (f : M -> Real)
    (hessF :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :
    Prop :=
  laplacian (I := I) cov g f x =
    metricTraceFirstTwo0SAt (I := I) g hessF Fin.elim0



def ScalarLaplacianRealizesTraceAtInBasis
    {Idx : Type*} [Fintype Idx]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (f : M -> Real)
    (hessF :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :
    Prop :=
  laplacian (I := I) cov g f x =
    metricTrace0S2InBasis (I := I) basis gInv hessF Fin.elim0



theorem scalar_laplacian_trace_of_hessian
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    {x : M}
    (f : M -> Real)
    (hessF :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (htrace :
      laplacian (I := I) cov g f x =
        metricTraceFirstTwo0SAt (I := I) g hessF Fin.elim0) :
    ScalarLaplacianRealizesTraceAt (I := I) cov g f hessF :=
  htrace


theorem scalar_laplacian_trace_of_pair
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    {x : M}
    (f : M -> Real)
    (hessF :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (htrace :
      laplacian (I := I) cov g f x =
        scalarLapTraceAt (I := I) g hessF) :
    ScalarLaplacianRealizesTraceAt (I := I) cov g f hessF := by
  unfold ScalarLaplacianRealizesTraceAt
  rw [htrace, scalarLapTraceAt_eq_firstTwo]



theorem ScalarLaplacianRealizesTraceAt.eq_trace
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    {x : M}
    (f : M -> Real)
    (hessF :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (h : ScalarLaplacianRealizesTraceAt (I := I) cov g f hessF) :
    laplacian (I := I) cov g f x =
      scalarLapTraceAt (I := I) g hessF := by
  unfold ScalarLaplacianRealizesTraceAt at h
  rw [h, traceFirstTwo_elim0]
  rfl




theorem lapTrace_of_slots
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    {x : M} {s : ℕ}
    (f : M -> Real)
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (tail : Fin s -> TangentSpace I x)
    (hessF :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (hlap : ScalarLaplacianRealizesTraceAt (I := I) cov g f hessF)
    (hslots :
      ∀ X Y : TangentSpace I x,
        T (metricTraceInput (I := I) X Y tail) =
          hessF (vec2 (I := I) X Y)) :
    metricTraceFirstTwo0SAt (I := I) g T tail =
      laplacian (I := I) cov g f x := by
  classical
  have hfreeze : freezeFirstTwo0S (I := I) T tail = hessF := by
    let basis : Module.Basis (Fin (Module.finrank Real (TangentSpace I x))) Real
        (TangentSpace I x) :=
      Module.finBasis Real (TangentSpace I x)
    apply ext0S_basis (I := I) basis
    intro slots
    simp only [component0S_apply]
    have hslot_vec :
        (fun a : Fin 2 => basis (slots a)) =
          vec2 (I := I) (basis (slots 0)) (basis (slots 1)) := by
      funext a
      fin_cases a <;> rfl
    rw [hslot_vec, freezeFirstTwo0S_apply]
    exact hslots (basis (slots 0)) (basis (slots 1))
  have htrace :
      metricTraceFirstTwo0SAt (I := I) g T tail =
        scalarLapTraceAt (I := I) g hessF := by
    rw [metricTraceFirstTwo0SAt, hfreeze, scalarLapTraceAt]
  exact htrace.trans
    ((ScalarLaplacianRealizesTraceAt.eq_trace (I := I) cov g f hessF hlap).symm)


theorem ScalarLaplacianRealizesTraceAt.toInBasis
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis_gen (I := I) g x basis gInv)
    (f : M -> Real)
    (hessF :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (h : ScalarLaplacianRealizesTraceAt (I := I) cov g f hessF) :
    ScalarLaplacianRealizesTraceAtInBasis (I := I) cov g basis gInv f hessF := by
  unfold ScalarLaplacianRealizesTraceAtInBasis
  rw [h, metricTrace0S2InBasis_eq_metricTrace (I := I) g basis gInv hinv hessF Fin.elim0]



def SmoothBasisFieldsAt
    {Idx : Type*} [Fintype Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (X : Idx -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _)) : Prop :=
  ∀ i : Idx, X i x = basis i

private theorem hessian_component_eq_inner_cov_gradient
    {Idx : Type*} [Fintype Idx]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    (hmc : DifferentialGeometry.Integral.Connection.IsMetricCompatible_gen (I := I) cov g)
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (f : M -> Real)
    (duSec : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (∞ : WithTop ℕ∞) 1)
    (hessF : (y : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 y)
    (X : Idx -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (hfields : SmoothBasisFieldsAt (I := I) basis X)
    (hdu : DuFieldRealizes (I := I) f duSec)
    (hHess : HessianRealizesNablaDuAt (I := I) cov duSec hessF x)
    (hgrad : MDiffAt (T% fun y : M => gradientFun (I := I) g f y) x)
    (i j : Idx) :
    hessF x (vec2 (I := I) (basis i) (basis j)) =
      g.inner x ((cov (fun y : M => gradientFun (I := I) g f y) x) (basis i))
        (basis j) := by
  classical
  let G : (y : M) -> TangentSpace I y := fun y => gradientFun (I := I) g f y
  have hXi : MDiffAt (T% fun y : M => X i y) x :=
    (X i).contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hXj : MDiffAt (T% fun y : M => X j y) x :=
    (X j).contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hfun :
      (fun y : M => duSec y (fun _ : Fin 1 => X j y)) =
        fun y : M => g.inner y (G y) (X j y) := by
    funext y
    rw [hdu y]
    exact differential1FormFun_apply_eq_inner_gradientFun (I := I) g f y (X j y)
  have hmetric := DifferentialGeometry.Integral.Connection.metric_compatible_apply
    (I := I) hmc (fun y : M => X i y) G (fun y : M => X j y) hXi hgrad hXj
  have hmetric_ext :
      extDerivFun (I := I) (fun y : M => g.inner y (G y) (X j y)) x (X i x) =
        g.inner x (cov G x (X i x)) (X j x) +
          g.inner x (G x) (cov (fun y : M => X j y) x (X i x)) := by
    rw [extDerivFun_real_eq_mfderiv]
    exact hmetric
  have hnabla_eval :
      nablaDuAt (I := I) cov (X i) duSec x (fun _ : Fin 1 => X j x) =
        extDerivFun (I := I) (fun y : M => duSec y (fun _ : Fin 1 => X j y)) x
            (X i x) -
          duSec x (fun _ : Fin 1 => (cov (fun y : M => X j y) x) (X i x)) := by
    simpa [nablaDuAt] using
      nabla0SFun_one_eval_smooth_slots (I := I) cov (X i) (X j) duSec x
  have hcorr :
      duSec x (fun _ : Fin 1 => (cov (fun y : M => X j y) x) (X i x)) =
        g.inner x (G x) (cov (fun y : M => X j y) x (X i x)) := by
    rw [hdu x]
    exact differential1FormFun_apply_eq_inner_gradientFun
      (I := I) g f x ((cov (fun y : M => X j y) x) (X i x))
  calc
    hessF x (vec2 (I := I) (basis i) (basis j))
        = hessF x (vec2 (I := I) (X i x) (X j x)) := by
            rw [hfields i, hfields j]
    _ = nablaDuAt (I := I) cov (X i) duSec x (fun _ : Fin 1 => X j x) := by
            exact hHess (X i) (X j x)
    _ = extDerivFun (I := I) (fun y : M => duSec y (fun _ : Fin 1 => X j y)) x
            (X i x) -
          duSec x (fun _ : Fin 1 => (cov (fun y : M => X j y) x) (X i x)) := by
            exact hnabla_eval
    _ = extDerivFun (I := I) (fun y : M => g.inner y (G y) (X j y)) x
            (X i x) -
          g.inner x (G x) (cov (fun y : M => X j y) x (X i x)) := by
            rw [hfun, hcorr]
    _ = g.inner x (cov G x (X i x)) (X j x) := by
            rw [hmetric_ext]
            ring
    _ = g.inner x ((cov (fun y : M => gradientFun (I := I) g f y) x) (basis i))
          (basis j) := by
            rw [hfields i, hfields j]







theorem scalarLaplacianRealizesTraceAt_of_nablaDu
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    (hmc : DifferentialGeometry.Integral.Connection.IsMetricCompatible_gen (I := I) cov g)
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis_gen (I := I) g x basis gInv)
    (f : M -> Real)
    (duSec : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (∞ : WithTop ℕ∞) 1)
    (hessF : (y : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 y)
    (X : Idx -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (hfields : SmoothBasisFieldsAt (I := I) basis X)
    (hdu : DuFieldRealizes (I := I) f duSec)
    (hHess : HessianRealizesNablaDuAt (I := I) cov duSec hessF x)
    (hgrad : MDiffAt (T% fun y : M => gradientFun (I := I) g f y) x) :
    ScalarLaplacianRealizesTraceAt (I := I) cov g f (hessF x) := by
  classical
  unfold ScalarLaplacianRealizesTraceAt
  rw [← metricTrace0S2InBasis_eq_metricTrace (I := I) g basis gInv hinv
    (hessF x) Fin.elim0]
  unfold laplacian divergence metricTrace0S2InBasis
  rw [linearMap_trace_eq_sum_inv_inner_apply (I := I) g x basis gInv hinv
    (cov (fun y : M => gradientFun (I := I) g f y) x).toLinearMap]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  have hinput :
      metricTraceInput (I := I) (basis i) (basis j) Fin.elim0 =
        vec2 (I := I) (basis i) (basis j) := by
    funext q
    fin_cases q
    · simp [metricTraceInput, vec2, DifferentialGeometry.Integral.Connection.vec2]
    · rfl
  rw [hinput]
  rw [hessian_component_eq_inner_cov_gradient
    (I := I) cov g hmc basis f duSec hessF X hfields hdu hHess hgrad i j]
  rfl


theorem scalarLapTraceAt_of_nablaDu
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    (hmc : DifferentialGeometry.Integral.Connection.IsMetricCompatible_gen (I := I) cov g)
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis_gen (I := I) g x basis gInv)
    (f : M -> Real)
    (duSec : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (∞ : WithTop ℕ∞) 1)
    (hessF : (y : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 y)
    (X : Idx -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (hfields : SmoothBasisFieldsAt (I := I) basis X)
    (hdu : DuFieldRealizes (I := I) f duSec)
    (hHess : HessianRealizesNablaDuAt (I := I) cov duSec hessF x)
    (hgrad : MDiffAt (T% fun y : M => gradientFun (I := I) g f y) x) :
    laplacian (I := I) cov g f x =
      scalarLapTraceAt (I := I) g (hessF x) :=
  ScalarLaplacianRealizesTraceAt.eq_trace (I := I) cov g f (hessF x)
    (scalarLaplacianRealizesTraceAt_of_nablaDu (I := I) cov g hmc basis gInv
      hinv f duSec hessF X hfields hdu hHess hgrad)






theorem scalarLap_canon
    [T2Space M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (g : SmoothRiemannianMetric I M)
    (hmc : DifferentialGeometry.Integral.Connection.IsMetricCompatible_gen (I := I) cov g)
    {x : M}
    (f : M -> Real)
    (hf : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) f)
    (hgrad : MDiffAt (T% fun y : M => gradientFun (I := I) g f y) x) :
    ScalarLaplacianRealizesTraceAt (I := I) cov g f
      (hessianSec (I := I) cov hcov f hf x) := by
  classical
  let basis :
      Module.Basis (CoordinateIdx (𝕜 := Real) E) Real (TangentSpace I x) :=
    DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis (I := I) x
  let gInv : CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real :=
    fun k l =>
      DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_component (I := I) g x k l
        (extChartAt I x x)
  let X :
      CoordinateIdx (𝕜 := Real) E ->
        ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
    fun i =>
      (ContMDiffSection.exists_eq_at_gen
        (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
        x (basis i)).choose
  have hfields : SmoothBasisFieldsAt (I := I) basis X := by
    intro i
    dsimp [X]
    exact
      (ContMDiffSection.exists_eq_at_gen
        (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
        x (basis i)).choose_spec
  exact scalarLaplacianRealizesTraceAt_of_nablaDu (I := I) cov g hmc basis gInv
    (DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_metricInverseInBasis_center
      (I := I) g x)
    f (duSec (I := I) f hf)
    (fun y : M => hessianSec (I := I) cov hcov f hf y)
    X hfields (duSec_realizes (I := I) f hf)
    (hessianSec_realizesAt (I := I) cov hcov f hf x) hgrad



theorem scalarLap_smooth
    [T2Space M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (g : SmoothRiemannianMetric I M)
    (hmc : DifferentialGeometry.Integral.Connection.IsMetricCompatible_gen (I := I) cov g)
    {x : M}
    (f : M -> Real)
    (hf : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) f) :
    ScalarLaplacianRealizesTraceAt (I := I) cov g f
      (hessianSec (I := I) cov hcov f hf x) := by
  exact scalarLap_canon (I := I) cov hcov g hmc f hf
    (gradientFun_mdiffAt (I := I) g hf x)



theorem lap_sub_conn
    [T2Space M]
    (cov cov' : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (hcov' : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov'
      (∞ : WithTop ℕ∞))
    (g g' : SmoothRiemannianMetric I M)
    (hmc : DifferentialGeometry.Integral.Connection.IsMetricCompatible_gen
      (I := I) cov g)
    (hmc' : DifferentialGeometry.Integral.Connection.IsMetricCompatible_gen
      (I := I) cov' g')
    (u : M -> Real) (hu : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) u)
    (x : M) :
    laplacian (I := I) cov g u x - laplacian (I := I) cov' g' u x =
      (scalarLapTraceAt (I := I) g
          (hessianSec (I := I) cov' hcov' u hu x) -
        scalarLapTraceAt (I := I) g'
          (hessianSec (I := I) cov' hcov' u hu x)) -
      scalarLapTraceAt (I := I) g
        (connectionDifferenceOutput (I := I)
          (CovariantDerivative.difference cov cov' x) (duSec (I := I) u hu x)) := by
  have hlap :
      laplacian (I := I) cov g u x =
        scalarLapTraceAt (I := I) g (hessianSec (I := I) cov hcov u hu x) :=
    (scalarLap_smooth (I := I) cov hcov g hmc (x := x) u hu).eq_trace
  have hlap' :
      laplacian (I := I) cov' g' u x =
        scalarLapTraceAt (I := I) g' (hessianSec (I := I) cov' hcov' u hu x) :=
    (scalarLap_smooth (I := I) cov' hcov' g' hmc' (x := x) u hu).eq_trace
  have hh := hess_sub_conn (I := I) cov cov' hcov hcov' u hu x
  have hHess :
      hessianSec (I := I) cov hcov u hu x =
        hessianSec (I := I) cov' hcov' u hu x -
          connectionDifferenceOutput (I := I)
            (CovariantDerivative.difference cov cov' x) (duSec (I := I) u hu x) := by
    calc
      hessianSec (I := I) cov hcov u hu x =
          (hessianSec (I := I) cov hcov u hu x -
            hessianSec (I := I) cov' hcov' u hu x) +
              hessianSec (I := I) cov' hcov' u hu x := by abel
      _ = -(connectionDifferenceOutput (I := I)
            (CovariantDerivative.difference cov cov' x) (duSec (I := I) u hu x)) +
              hessianSec (I := I) cov' hcov' u hu x := by rw [hh]
      _ = hessianSec (I := I) cov' hcov' u hu x -
          connectionDifferenceOutput (I := I)
            (CovariantDerivative.difference cov cov' x) (duSec (I := I) u hu x) := by
        abel
  rw [hlap, hlap', hHess]
  simp only [scalarLapTraceAt, metricTracePair0SAt, inner0S,
    MetricFiberData.inner, map_sub]
  ring





theorem lapTrace_nablaSec
    [T2Space M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    (hmc : DifferentialGeometry.Integral.Connection.IsMetricCompatible_gen (I := I) cov g)
    (f : M -> Real)
    (duSec : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (∞ : WithTop ℕ∞) 1)
    (hessF : (y : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 y)
    (hdu : DuFieldRealizes (I := I) f duSec)
    (hHess : ∀ y : M, HessianRealizesNablaDuAt (I := I) cov duSec hessF y)
    (hgrad : ∀ y : M, MDiffAt (T% fun z : M => gradientFun (I := I) g f z) y) :
    ∀ y : M,
      laplacian (I := I) cov g f y =
        scalarLapTraceAt (I := I) g (hessF y) := by
  intro y
  classical
  let basis :
      Module.Basis (CoordinateIdx (𝕜 := Real) E) Real (TangentSpace I y) :=
    DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis (I := I) y
  let gInv : CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real :=
    fun k l =>
      DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_component (I := I) g y k l
        (extChartAt I y y)
  let X :
      CoordinateIdx (𝕜 := Real) E ->
        ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
    fun i =>
      (ContMDiffSection.exists_eq_at_gen
        (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
        y (basis i)).choose
  have hfields : SmoothBasisFieldsAt (I := I) basis X := by
    intro i
    dsimp [X]
    exact
      (ContMDiffSection.exists_eq_at_gen
        (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
        y (basis i)).choose_spec
  exact scalarLapTraceAt_of_nablaDu (I := I) cov g hmc basis gInv
    (DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_metricInverseInBasis_center (I := I) g y)
    f duSec hessF X hfields hdu (hHess y) (hgrad y)

end DifferentialGeometry.Integral.Connection
