import DifferentialGeometry.Geometry.Connection.Laplacian.TensorConnLaplacian
import DifferentialGeometry.Geometry.Connection.LeviCivita.Smooth.Connection
import DifferentialGeometry.Geometry.Operator.HessianTraceRealization
import DifferentialGeometry.Tensor.RSTensor.Field









noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Bundle Manifold CovariantDerivative Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E


theorem nablaRS_toRS0
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞]
    {s : ℕ}
    (A : Tensor0SField ∞ s (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M))
    (x : M) (v : TangentSpace I x) :
    TensorRSNabla.tensorRSCovariantDerivative I M 0 s cov
        (A.toTensorRSField ∞) x v =
      Tensor0SSpace.toRS0
        (Tensor0SNabla.tensor0SCovariantDerivative I M s cov A x v) := by
  classical
  let one0 : Tensor0SField ∞ 0 (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) :=
    Tensor0SField.one0 (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) ∞
  have hone_eval (y : M) : tensor0SSpace_evalScalar y (one0 y) = 1 := by
    rw [Tensor0SSpace.evalScalar_apply]
    change Tensor0SField.toScalarField ∞ one0 y = 1
    have h := Tensor0SField.toScalarField_fromScalarField
      (I := I) (M := M) ∞ (fun _ : M => (1 : ℝ)) contMDiff_const
    exact congrFun h y
  have hone_scalar : Tensor0SNabla.scalarFn I M (fun y => one0 y) = fun _ => 1 := by
    funext y
    rw [Tensor0SNabla.scalarFn_eq_apply_zero]
    exact hone_eval y
  have hone_nabla :
      Tensor0SNabla.tensor0SCovariantDerivative I M 0 cov one0 x v = 0 := by
    rw [Tensor0SNabla.tensor0SCovariantDerivative_apply_zero, hone_scalar]
    simp [extDerivFun]
  have hsection :
      (fun y : M =>
        (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y from
          A.toTensorRSField ∞ y) (one0 y)) = fun y => A y := by
    funext y
    rw [Tensor0SField.toRS0_apply, hone_eval, one_smul]
  have hunit :
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        TensorRSNabla.tensorRSCovariantDerivative I M 0 s cov
          (A.toTensorRSField ∞) x v) (one0 x) =
        Tensor0SNabla.tensor0SCovariantDerivative I M s cov A x v := by
    rw [TensorRSNabla.tensorRSCovariantDerivative_apply I M 0 s cov
      (A.toTensorRSField ∞) one0 x v]
    rw [hsection, hone_nabla, map_zero, sub_zero]
  apply ContinuousLinearMap.ext
  intro c
  have heval : tensor0SSpace_evalScalar x c = Tensor0SNabla.tensor0Iso I M x c := by
    rw [Tensor0SSpace.evalScalar_apply]
    let S : (y : M) → Tensor0SSpace 0 I y := fun y =>
      (Tensor0SNabla.tensor0Iso I M y).symm (Tensor0SNabla.tensor0Iso I M x c)
    have hSx : S x = c := by simp [S]
    have h := Tensor0SNabla.scalarFn_eq_apply_zero I M S x
    rw [Tensor0SNabla.scalarFn_apply, hSx] at h
    exact (congrArg c (Subsingleton.elim Fin.elim0 0)).trans h.symm
  have hone_iso : Tensor0SNabla.tensor0Iso I M x (one0 x) = 1 := by
    rw [← Tensor0SNabla.scalarFn_apply]
    rw [hone_scalar]
  have hc : tensor0SSpace_evalScalar x c • one0 x = c := by
    apply (Tensor0SNabla.tensor0Iso I M x).injective
    rw [map_smul, heval, hone_iso, smul_eq_mul, mul_one]
  calc
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        TensorRSNabla.tensorRSCovariantDerivative I M 0 s cov
          (A.toTensorRSField ∞) x v) c =
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
          TensorRSNabla.tensorRSCovariantDerivative I M 0 s cov
            (A.toTensorRSField ∞) x v)
          (tensor0SSpace_evalScalar x c • one0 x) := by rw [hc]
    _ = tensor0SSpace_evalScalar x c •
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
          TensorRSNabla.tensorRSCovariantDerivative I M 0 s cov
            (A.toTensorRSField ∞) x v) (one0 x) := by rw [map_smul]
    _ = tensor0SSpace_evalScalar x c •
        Tensor0SNabla.tensor0SCovariantDerivative I M s cov A x v := by rw [hunit]
    _ = Tensor0SSpace.toRS0
        (Tensor0SNabla.tensor0SCovariantDerivative I M s cov A x v) c := rfl

private noncomputable def cov0SAlong
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞]
    {s : ℕ}
    (X : ContMDiffSection I E ∞ (TangentSpace I : M → Type _))
    (A : Tensor0SField ∞ s (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)) :
    Tensor0SField ∞ s (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) := by
  let cov0 := Tensor0SNabla.tensor0SCovariantDerivative I M s cov
  refine ⟨fun y => covApply cov0 X A y, ?_⟩
  have hA : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel s ℝ E)) (∞ + 1)
      (fun y : M => TotalSpace.mk' (Tensor0SModel s ℝ E)
        (E := fun z : M => Tensor0SSpace s I z) y (A y)) := by
    simpa using A.contMDiff
  have hOn := covApply_contMDiffOn (cov := cov0) X.contMDiff hA
  rwa [contMDiffOn_univ] at hOn

@[simp]
private theorem cov0SAlong_apply
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞]
    {s : ℕ}
    (X : ContMDiffSection I E ∞ (TangentSpace I : M → Type _))
    (A : Tensor0SField ∞ s (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M))
    (x : M) :
    cov0SAlong cov X A x =
      Tensor0SNabla.tensor0SCovariantDerivative I M s cov A x (X x) :=
  rfl

variable [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M]

omit [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M]
  [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in


private theorem orthonormal_li
    (g : SmoothRiemannianMetric I M) {x : M}
    (frame : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (horth : ∀ i j, g.inner x (frame i) (frame j) = if i = j then 1 else 0) :
    LinearIndependent ℝ frame := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  have hpair : g.inner x (∑ i, c i • frame i) (frame j) = 0 := by
    rw [hc]
    simp
  rw [map_sum, ContinuousLinearMap.sum_apply, Finset.sum_eq_single j] at hpair
  · rw [ContinuousLinearMap.map_smul, ContinuousLinearMap.smul_apply,
      horth j j, if_pos rfl, smul_eq_mul, mul_one] at hpair
    exact hpair
  · intro i _ hij
    rw [ContinuousLinearMap.map_smul, ContinuousLinearMap.smul_apply,
      horth i j, if_neg (by simpa using hij), smul_zero]
  · intro hj
    exact absurd (Finset.mem_univ j) hj


private noncomputable def orthoFrameBasis
    (g : SmoothRiemannianMetric I M) (x : M) :
    Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x) :=
  basisOfLinearIndependentOfCardEqFinrank
    (b := fun i : Fin (Module.finrank ℝ E) =>
      smoothOrthoFrame (I := I) g x i x)
    (orthonormal_li (I := I) (M := M) g _
      (fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g x i j))
    (by rw [Fintype.card_fin]; rfl)

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
@[simp]
private theorem orthoBasis_apply
    (g : SmoothRiemannianMetric I M) (x : M)
    (i : Fin (Module.finrank ℝ E)) :
    orthoFrameBasis (I := I) (M := M) g x i =
      smoothOrthoFrame (I := I) g x i x := by
  unfold orthoFrameBasis
  rw [coe_basisOfLinearIndependentOfCardEqFinrank]


theorem rawLap_toRS0
    (g : SmoothRiemannianMetric I M) {s : ℕ}
    (A : Tensor0SField ∞ s (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M))
    (x : M) :
    rawTensorConnLap (I := I) g 0 s (fun y => A.toTensorRSField ∞ y) x =
      Tensor0SSpace.toRS0
        (∑ i : Fin (Module.finrank ℝ E), (
          Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)
              (cov0SAlong (LeviCivita (I := I) g)
                ⟨smoothOrthoFrame (I := I) g x i,
                  smoothOrthoFrame_smooth (I := I) g x i⟩ A)
              x (smoothOrthoFrame (I := I) g x i x) -
            Tensor0SNabla.tensor0SCovariantDerivative I M s
              (LeviCivita (I := I) g) A x
              ((LeviCivita (I := I) g).toFun
                (smoothOrthoFrame (I := I) g x i) x
                (smoothOrthoFrame (I := I) g x i x)))) := by
  classical
  let cov0 := Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)
  let covRS := TensorRSNabla.tensorRSCovariantDerivative I M 0 s (LeviCivita (I := I) g)
  let B : Fin (Module.finrank ℝ E) →
      ContMDiffSection I E ∞ (TangentSpace I : M → Type _) := fun i =>
    ⟨smoothOrthoFrame (I := I) g x i, smoothOrthoFrame_smooth (I := I) g x i⟩
  let dA : Fin (Module.finrank ℝ E) →
      Tensor0SField ∞ s (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) :=
    fun i => cov0SAlong (LeviCivita (I := I) g) (B i) A
  let W : Fin (Module.finrank ℝ E) → TangentSpace I x := fun i =>
    (LeviCivita (I := I) g).toFun (B i) x (B i x)
  have hfirst (i : Fin (Module.finrank ℝ E)) :
      covApply covRS (B i) (fun y => A.toTensorRSField ∞ y) =
        fun y => (dA i).toTensorRSField ∞ y := by
    funext y
    calc
      covApply covRS (B i) (fun z => A.toTensorRSField ∞ z) y =
          Tensor0SSpace.toRS0 (cov0 A y (B i y)) := by
            exact nablaRS_toRS0 (I := I) (M := M) (LeviCivita (I := I) g) A y (B i y)
      _ = (dA i).toTensorRSField ∞ y := by
        rw [Tensor0SField.toRS0_eq]
        rfl
  rw [rawTensorConnLap_def]
  apply ContinuousLinearMap.ext
  intro c
  rw [Tensor0SSpace.toRS0_apply, Finset.smul_sum,
    ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl ?_
  intro i _
  change
    (covRS (covApply covRS (B i) (fun y => A.toTensorRSField ∞ y)) x (B i x) -
      covRS (fun y => A.toTensorRSField ∞ y) x (W i)) c = _
  rw [hfirst i]
  rw [show covRS (fun y => (dA i).toTensorRSField ∞ y) x (B i x) =
      Tensor0SSpace.toRS0 (cov0 (dA i) x (B i x)) by
        exact nablaRS_toRS0 (I := I) (M := M) (LeviCivita (I := I) g)
          (dA i) x (B i x)]
  rw [show covRS (fun y => A.toTensorRSField ∞ y) x (W i) =
        Tensor0SSpace.toRS0
          (cov0 A x (W i)) by
        exact nablaRS_toRS0 (I := I) (M := M) (LeviCivita (I := I) g) A x
          (W i)]
  simp only [smul_sub]
  rfl



omit [NeZero (Module.finrank ℝ E)] in
private theorem cov0_diag_hess
    (g : SmoothRiemannianMetric I M)
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally
      (LeviCivita (I := I) g) ∞)
    {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (B : ContMDiffSection I E ∞ (TangentSpace I : M → Type _)) (x : M) :
    Tensor0SNabla.tensor0Iso I M x
        (Tensor0SNabla.tensor0SCovariantDerivative I M 0
              (LeviCivita (I := I) g)
              (cov0SAlong (LeviCivita (I := I) g) B
                (Tensor0SField.fromScalarField ∞ f hf))
              x (B x) -
          Tensor0SNabla.tensor0SCovariantDerivative I M 0
              (LeviCivita (I := I) g)
              (Tensor0SField.fromScalarField ∞ f hf) x
              ((LeviCivita (I := I) g).toFun B x (B x))) =
      hessianSec (I := I) (LeviCivita (I := I) g) hcov f hf x
        (vec2 (I := I) (B x) (B x)) := by
  let A : Tensor0SField ∞ 0 (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) :=
    Tensor0SField.fromScalarField ∞ f hf
  have hscalarA : Tensor0SNabla.scalarFn I M (fun y : M => A y) = f := by
    funext y
    rw [Tensor0SNabla.scalarFn_eq_apply_zero]
    change Tensor0SField.toScalarField ∞ A y = f y
    exact congrFun (Tensor0SField.toScalarField_fromScalarField ∞ f hf) y
  have hscalarDA :
      Tensor0SNabla.scalarFn I M
          (fun y : M => cov0SAlong (LeviCivita (I := I) g) B A y) =
        fun y : M => extDerivFun (I := I) f y (B y) := by
    funext y
    rw [Tensor0SNabla.scalarFn_apply, cov0SAlong_apply,
      Tensor0SNabla.tensor0SCovariantDerivative_apply_zero,
      ContinuousLinearEquiv.apply_symm_apply, hscalarA]
  change Tensor0SNabla.tensor0Iso I M x
      (Tensor0SNabla.tensor0SCovariantDerivative I M 0
            (LeviCivita (I := I) g)
            (cov0SAlong (LeviCivita (I := I) g) B A) x (B x) -
        Tensor0SNabla.tensor0SCovariantDerivative I M 0
            (LeviCivita (I := I) g) A x
            ((LeviCivita (I := I) g).toFun B x (B x))) = _
  rw [map_sub, Tensor0SNabla.tensor0SCovariantDerivative_apply_zero,
    Tensor0SNabla.tensor0SCovariantDerivative_apply_zero,
    ContinuousLinearEquiv.apply_symm_apply,
    ContinuousLinearEquiv.apply_symm_apply, hscalarDA, hscalarA]
  rw [(hessianSec_realizesAt (I := I) (LeviCivita (I := I) g)
    hcov f hf x) B (B x)]
  change extDerivFun (I := I) (fun y : M => extDerivFun (I := I) f y (B y))
      x (B x) -
    extDerivFun (I := I) f x ((LeviCivita (I := I) g).toFun B x (B x)) =
      (nabla0SFun (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
        1 (LeviCivita (I := I) g) B (duSec (I := I) f hf) x)
          (fun _ : Fin 1 => B x)
  rw [DifferentialGeometry.Tensor.Coordinates.nabla0SFun_one_eval_smooth_slots
    (I := I) (LeviCivita (I := I) g) B B (duSec (I := I) f hf) x]
  have hpairing :
      (fun y : M => duSec (I := I) f hf y (fun _ : Fin 1 => B y)) =
        fun y : M => extDerivFun (I := I) f y (B y) := by
    funext y
    rw [duSec_apply]
    exact differential1FormFun_apply_eq_extDerivFun (I := I) f y (B y)
  rw [hpairing, duSec_apply,
    differential1FormFun_apply_eq_extDerivFun]



omit [NeZero (Module.finrank ℝ E)] in
theorem secondRS_scalar
    (g : SmoothRiemannianMetric I M)
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally
      (LeviCivita (I := I) g) ∞)
    {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (B : ContMDiffSection I E ∞ (TangentSpace I : M → Type _)) (x : M) :
    (TensorRSNabla.tensorRSCovariantDerivative I M 0 0
        (LeviCivita (I := I) g)).toFun
          (covApply (TensorRSNabla.tensorRSCovariantDerivative I M 0 0
            (LeviCivita (I := I) g)) B
            (fun y : M =>
              (Tensor0SField.fromScalarField ∞ f hf).toTensorRSField ∞ y)) x (B x) -
        (TensorRSNabla.tensorRSCovariantDerivative I M 0 0
          (LeviCivita (I := I) g)).toFun
          (fun y : M =>
            (Tensor0SField.fromScalarField ∞ f hf).toTensorRSField ∞ y) x
          ((LeviCivita (I := I) g).toFun B x (B x)) =
      Tensor0SSpace.toRS0
        ((Tensor0SNabla.tensor0Iso I M x).symm
          (hessianSec (I := I) (LeviCivita (I := I) g) hcov f hf x
            (vec2 (I := I) (B x) (B x)))) := by
  classical
  let A : Tensor0SField ∞ 0 (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) :=
    Tensor0SField.fromScalarField ∞ f hf
  let cov0 := Tensor0SNabla.tensor0SCovariantDerivative I M 0
    (LeviCivita (I := I) g)
  let covRS := TensorRSNabla.tensorRSCovariantDerivative I M 0 0
    (LeviCivita (I := I) g)
  let dA : Tensor0SField ∞ 0 (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) :=
    cov0SAlong (LeviCivita (I := I) g) B A
  have hfirst :
      covApply covRS B (fun y => A.toTensorRSField ∞ y) =
        fun y => dA.toTensorRSField ∞ y := by
    funext y
    calc
      covApply covRS B (fun z => A.toTensorRSField ∞ z) y =
          Tensor0SSpace.toRS0 (cov0 A y (B y)) := by
            exact nablaRS_toRS0 (I := I) (M := M)
              (LeviCivita (I := I) g) A y (B y)
      _ = dA.toTensorRSField ∞ y := by
        rw [Tensor0SField.toRS0_eq]
        rfl
  have harg :
      cov0 dA x (B x) -
          cov0 A x ((LeviCivita (I := I) g).toFun B x (B x)) =
        (Tensor0SNabla.tensor0Iso I M x).symm
          (hessianSec (I := I) (LeviCivita (I := I) g) hcov f hf x
            (vec2 (I := I) (B x) (B x))) := by
    apply (Tensor0SNabla.tensor0Iso I M x).injective
    rw [map_sub, ContinuousLinearEquiv.apply_symm_apply]
    simpa [A, cov0, dA] using
      (cov0_diag_hess (I := I) (M := M) g hcov hf B x)
  change covRS (covApply covRS B (fun y => A.toTensorRSField ∞ y)) x (B x) -
      covRS (fun y => A.toTensorRSField ∞ y) x
        ((LeviCivita (I := I) g).toFun B x (B x)) = _
  rw [hfirst]
  rw [show covRS (fun y => dA.toTensorRSField ∞ y) x (B x) =
      Tensor0SSpace.toRS0 (cov0 dA x (B x)) by
        exact nablaRS_toRS0 (I := I) (M := M)
          (LeviCivita (I := I) g) dA x (B x)]
  rw [show covRS (fun y => A.toTensorRSField ∞ y) x
        ((LeviCivita (I := I) g).toFun B x (B x)) =
      Tensor0SSpace.toRS0
        (cov0 A x ((LeviCivita (I := I) g).toFun B x (B x))) by
        exact nablaRS_toRS0 (I := I) (M := M)
          (LeviCivita (I := I) g) A x
          ((LeviCivita (I := I) g).toFun B x (B x))]
  rw [← harg]
  apply ContinuousLinearMap.ext
  intro c
  rw [ContinuousLinearMap.sub_apply, Tensor0SSpace.toRS0_apply,
    Tensor0SSpace.toRS0_apply, Tensor0SSpace.toRS0_apply, smul_sub]




theorem rawLap_scalar
    (g : SmoothRiemannianMetric I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M) :
    rawTensorConnLap (I := I) g 0 0
        (fun y : M =>
          (Tensor0SField.fromScalarField ∞ f hf).toTensorRSField ∞ y) x =
      Tensor0SSpace.toRS0
        ((Tensor0SNabla.tensor0Iso I M x).symm
          (laplacian (I := I) (LeviCivita (I := I) g) g f x)) := by
  classical
  let A : Tensor0SField ∞ 0 (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) :=
    Tensor0SField.fromScalarField ∞ f hf
  let hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally
      (LeviCivita (I := I) g) ∞ := by
    simpa [LeviCivita] using
      (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
        (I := I) (M := M) g)
  let Hess := hessianSec (I := I) (LeviCivita (I := I) g) hcov f hf
  change rawTensorConnLap (I := I) g 0 0
      (fun y : M => A.toTensorRSField ∞ y) x = _
  rw [rawLap_toRS0 (I := I) (M := M) g A x]
  apply congrArg Tensor0SSpace.toRS0
  apply (Tensor0SNabla.tensor0Iso I M x).injective
  rw [map_sum, ContinuousLinearEquiv.apply_symm_apply]
  calc
    ∑ i : Fin (Module.finrank ℝ E),
        Tensor0SNabla.tensor0Iso I M x
          (Tensor0SNabla.tensor0SCovariantDerivative I M 0
                (LeviCivita (I := I) g)
                (cov0SAlong (LeviCivita (I := I) g)
                  ⟨smoothOrthoFrame (I := I) g x i,
                    smoothOrthoFrame_smooth (I := I) g x i⟩ A)
                x (smoothOrthoFrame (I := I) g x i x) -
            Tensor0SNabla.tensor0SCovariantDerivative I M 0
                (LeviCivita (I := I) g) A x
                ((LeviCivita (I := I) g).toFun
                  (smoothOrthoFrame (I := I) g x i) x
                  (smoothOrthoFrame (I := I) g x i x))) =
      ∑ i : Fin (Module.finrank ℝ E),
        Hess x (vec2 (I := I)
          (smoothOrthoFrame (I := I) g x i x)
          (smoothOrthoFrame (I := I) g x i x)) := by
        refine Finset.sum_congr rfl ?_
        intro i _
        simpa [A, Hess] using
          (cov0_diag_hess (I := I) (M := M) g hcov hf
            ⟨smoothOrthoFrame (I := I) g x i,
              smoothOrthoFrame_smooth (I := I) g x i⟩ x)
    _ = scalarLapTraceAt (I := I) g (Hess x) := by
      let basis := orthoFrameBasis (I := I) (M := M) g x
      have horth : ∀ i j : Fin (Module.finrank ℝ E),
          g.inner x (basis i) (basis j) = if i = j then 1 else 0 := by
        intro i j
        rw [orthoBasis_apply, orthoBasis_apply]
        exact smoothOrthoFrame_orthonormal_at_center (I := I) g x i j
      have hinv : MetricInverseInBasis_gen (I := I) g x basis
          (identityInvMetric (Idx := Fin (Module.finrank ℝ E))) := by
        intro i j
        constructor <;> simp [identityInvMetric, diagonalInvMetric, horth]
      rw [scalarLapTraceAt,
        metricTracePair0SAt_eq_sum_basis (I := I) g basis
          (identityInvMetric (Idx := Fin (Module.finrank ℝ E))) hinv]
      simp only [basis, orthoBasis_apply]
      symm
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [Finset.sum_eq_single i]
      · rw [identityInvMetric_apply_self, one_mul]
      · intro j _ hji
        rw [identityInvMetric,
          diagonalInvMetric_eq_zero_of_ne (fun h => hji h.symm), zero_mul]
      · intro hi
        exact absurd (Finset.mem_univ i) hi
    _ = laplacian (I := I) (LeviCivita (I := I) g) g f x := by
      have hmc : IsMetricCompatible_gen (I := I) (LeviCivita (I := I) g) g := by
        simpa [LeviCivita] using
          (leviCivitaConnectionOfMetric_isMetricCompatible (I := I) g)
      have hreal := scalarLap_smooth (I := I) (M := M)
        (LeviCivita (I := I) g) hcov g hmc f hf (x := x)
      simpa [Hess] using
        (ScalarLaplacianRealizesTraceAt.eq_trace
          (I := I) (LeviCivita (I := I) g) g f (Hess x) hreal).symm

end Connection
end Integral
end DifferentialGeometry

end
