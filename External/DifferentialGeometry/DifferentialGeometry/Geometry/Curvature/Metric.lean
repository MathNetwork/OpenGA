import DifferentialGeometry.Geometry.Curvature.Realized.CurvatureProducers
import DifferentialGeometry.Geometry.Operator.RoughLaplacian
import DifferentialGeometry.Tensor.RSTensor.MetricTrace.Connection
import DifferentialGeometry.Tensor.RSTensor.MetricTrace.Trace04
import DifferentialGeometry.Tensor.RSTensor.MetricTrace.NablaTrace02
import DifferentialGeometry.Tensor.RSTensor.MetricTrace.Higher
import DifferentialGeometry.Geometry.Connection.LeviCivita.Curvature.LeviCivita
import DifferentialGeometry.Geometry.Connection.LeviCivita.Curvature.Realized
import DifferentialGeometry.Geometry.Connection.LeviCivita.Smooth.MetricFlatBasis
import DifferentialGeometry.Geometry.Connection.LeviCivita.Smooth.Connection
import DifferentialGeometry.Geometry.Connection.LeviCivita.Smooth.MetricCoord
import DifferentialGeometry.Geometry.Connection.LeviCivita.Smooth.Model
import DifferentialGeometry.Geometry.Connection.LeviCivita.Smooth.Christoffel
import DifferentialGeometry.Geometry.Coordinates.NablaComponents.TwoTensor
import DifferentialGeometry.Bundle.PartialMfderiv.FixedBase

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedFintypeInType false









noncomputable section

namespace DifferentialGeometry.Integral.Connection

open Bundle Tensor0SBundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]


noncomputable def metricCov (g : SmoothRiemannianMetric I M) :
    CovariantDerivative I E (TangentSpace I : M -> Type _) :=
  DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) g


omit [SigmaCompactSpace M] [T2Space M] in
theorem metricCov_smooth (g : SmoothRiemannianMetric I M) :
    CovariantDerivative.ContMDiffCovariantDerivativeLocally
      (I := I) (E := E) (M := M) (metricCov (I := I) (M := M) g) ∞ := by
  simpa [metricCov] using
    DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
      (I := I) (M := M) g



omit [SigmaCompactSpace M] [T2Space M] in
theorem metricCov_congr_nhds
    (g : SmoothRiemannianMetric I M)
    {Y Y' : (y : M) → TangentSpace I y} {x : M}
    (hY : MDifferentiableAt I I.tangent (T% Y) x)
    (hY' : MDifferentiableAt I I.tangent (T% Y') x)
    (hEq : Y =ᶠ[nhds x] Y') :
    (metricCov (I := I) (M := M) g).toFun Y x =
      (metricCov (I := I) (M := M) g).toFun Y' x := by
  exact (metricCov (I := I) (M := M) g).isCovariantDerivativeOnUniv.congr_of_eventuallyEq
    hY hY' Filter.univ_mem hEq


noncomputable def metricRm13At (g : SmoothRiemannianMetric I M) (x : M) :
    Tensor13At (I := I) (M := M) x :=
  DifferentialGeometry.Integral.Connection.CovariantDerivative.riemannCurvatureAt
    (metricCov (I := I) (M := M) g)
    (metricCov_smooth (I := I) (M := M) g) x


noncomputable def metricRm04At (g : SmoothRiemannianMetric I M) (x : M) :
    Tensor04At (I := I) (M := M) x :=
  DifferentialGeometry.Integral.Connection.CovariantDerivative.riemannCurvature04At
    (I := I) g
    (metricCov (I := I) (M := M) g)
    (metricCov_smooth (I := I) (M := M) g) x


noncomputable def metricRicciAt (g : SmoothRiemannianMetric I M) (x : M) :
    Tensor02At (I := I) (M := M) x :=
  DifferentialGeometry.Integral.Connection.CovariantDerivative.ricciCurvatureAt
    (I := I)
    (metricCov (I := I) (M := M) g)
    (metricCov_smooth (I := I) (M := M) g) x


noncomputable def metricScalarAt (g : SmoothRiemannianMetric I M) (x : M) :
    Real :=
  DifferentialGeometry.Integral.Connection.metricTracePair0SAt (I := I) g (metricRicciAt (I := I) (M := M) g x)






omit [SigmaCompactSpace M] [T2Space M] in
theorem metricRicciAt_eq_trace (g : SmoothRiemannianMetric I M) (x : M) :
    metricRicciAt (I := I) g x
      = DifferentialGeometry.Integral.Connection.ricciFromRm13At
          (metricRm13At (I := I) (M := M) g x) := rfl




omit [SigmaCompactSpace M] [T2Space M] in
theorem metricScalarAt_def (g : SmoothRiemannianMetric I M) (x : M) :
    metricScalarAt (I := I) g x
      = DifferentialGeometry.Integral.Connection.metricTracePair0SAt (I := I) g
          (metricRicciAt (I := I) (M := M) g x) := rfl


noncomputable def metricRm04 (g : SmoothRiemannianMetric I M) :
    DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M) :=
  DifferentialGeometry.Integral.Connection.CovariantDerivative.rm04Section
    (I := I) g (metricCov (I := I) (M := M) g)
    (metricCov_smooth (I := I) (M := M) g)


noncomputable def metricRm13 (g : SmoothRiemannianMetric I M) :
    DifferentialGeometry.Integral.Connection.Tensor13Section (I := I) (M := M) :=
  DifferentialGeometry.Integral.Connection.CovariantDerivative.rm13Section
    (I := I) (M := M) (metricCov (I := I) (M := M) g)
    (metricCov_smooth (I := I) (M := M) g)






noncomputable def metricRm04StdAt
    (g : SmoothRiemannianMetric I M) (x : M)
    (X Y Z W : TangentSpace I x) : Real :=
  tensor04StdAt (I := I) (M := M)
    (metricRm04At (I := I) (M := M) g x) X Y Z W


noncomputable def metricRicci (g : SmoothRiemannianMetric I M) :
    DifferentialGeometry.Integral.Connection.Tensor02Section (I := I) (M := M) :=
  DifferentialGeometry.Integral.Connection.CovariantDerivative.ricciSection
    (I := I) (M := M) (metricCov (I := I) (M := M) g)
    (metricCov_smooth (I := I) (M := M) g)

omit [SigmaCompactSpace M] in
@[simp] theorem metricRm04_apply
    (g : SmoothRiemannianMetric I M) (x : M) :
    metricRm04 (I := I) (M := M) g x =
      metricRm04At (I := I) (M := M) g x := by
  simp [metricRm04, metricRm04At]

omit [SigmaCompactSpace M] [T2Space M] in
@[simp] theorem metricRm04StdAt_apply
    (g : SmoothRiemannianMetric I M) (x : M)
    (X Y Z W : TangentSpace I x) :
    metricRm04StdAt (I := I) (M := M) g x X Y Z W =
      metricRm04At (I := I) (M := M) g x (vec4 X Y Z W) := by
  rfl



noncomputable def metricRm04LastDualAt
    (g : SmoothRiemannianMetric I M) (x : M)
    (X Y Z : TangentSpace I x) :
    Module.Dual Real (TangentSpace I x) where
  toFun W := metricRm04StdAt (I := I) (M := M) g x X Y Z W
  map_add' W W' := by
    have h :=
      (metricRm04At (I := I) (M := M) g x).map_update_add
        (vec4 (I := I) X Y Z 0) (3 : Fin 4) W W'
    change
      metricRm04At (I := I) (M := M) g x
          (vec4 (I := I) X Y Z (W + W')) =
        metricRm04At (I := I) (M := M) g x
            (vec4 (I := I) X Y Z W) +
          metricRm04At (I := I) (M := M) g x
            (vec4 (I := I) X Y Z W')
    convert h using 1
  map_smul' c W := by
    have h :=
      (metricRm04At (I := I) (M := M) g x).map_update_smul
        (vec4 (I := I) X Y Z 0) (3 : Fin 4) c W
    change
      metricRm04At (I := I) (M := M) g x
          (vec4 (I := I) X Y Z (c • W)) =
        c * metricRm04At (I := I) (M := M) g x
            (vec4 (I := I) X Y Z W)
    convert h using 1

omit [SigmaCompactSpace M] [T2Space M] in
@[simp] theorem metricRm04LastDualAt_apply
    (g : SmoothRiemannianMetric I M) (x : M)
    (X Y Z W : TangentSpace I x) :
    metricRm04LastDualAt (I := I) (M := M) g x X Y Z W =
      metricRm04StdAt (I := I) (M := M) g x X Y Z W := by
  rfl

omit [SigmaCompactSpace M] in
@[simp] theorem metricRm13_apply
    (g : SmoothRiemannianMetric I M) (x : M) :
    metricRm13 (I := I) (M := M) g x =
      metricRm13At (I := I) (M := M) g x := by
  simp [metricRm13, metricRm13At]

omit [SigmaCompactSpace M] in
@[simp] theorem metricRicci_apply
    (g : SmoothRiemannianMetric I M) (x : M) :
    metricRicci (I := I) (M := M) g x =
      metricRicciAt (I := I) (M := M) g x := by
  simp [metricRicci, metricRicciAt]


noncomputable def metricCurvData
    (g : SmoothRiemannianMetric I M) :
    DifferentialGeometry.Integral.Connection.CurvatureSectionProducerData (I := I)
      (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) g) g where
  rm13 := metricRm13 (I := I) (M := M) g
  rm04 := metricRm04 (I := I) (M := M) g
  ricci := metricRicci (I := I) (M := M) g
  h_rm13 := by
    simpa [metricRm13, metricCov] using
      (DifferentialGeometry.Integral.Connection.rm13Section_realizes (I := I) (M := M)
        (cov := metricCov (I := I) (M := M) g)
        (hcov := metricCov_smooth (I := I) (M := M) g))
  h_rm04 := by
    simpa [metricRm04, metricCov] using
      (DifferentialGeometry.Integral.Connection.rm04Section_realizes (I := I) (M := M) g
        (cov := metricCov (I := I) (M := M) g)
        (hcov := metricCov_smooth (I := I) (M := M) g))
  h_ricci13 := by
    intro x
    simp [metricRicci, metricRm13]





omit [SigmaCompactSpace M] in
theorem metricScalar_smooth
    (g : SmoothRiemannianMetric I M) :
    ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
      (fun x : M => metricScalarAt (I := I) (M := M) g x) := by
  simpa [metricScalarAt] using
    DifferentialGeometry.Integral.Connection.trace02_smooth (I := I) (M := M) g
      (metricRicci (I := I) (M := M) g)




omit [SigmaCompactSpace M] in
theorem metricScalar_const_of_dScalar_zero
    [I.Boundaryless] [ConnectedSpace M]
    (g : SmoothRiemannianMetric I M)
    (hzero : ∀ x : M, ∀ X : TangentSpace I x,
      DifferentialGeometry.Integral.Connection.differential1FormFun (I := I)
          (fun y : M => metricScalarAt (I := I) (M := M) g y)
          x (fun _ : Fin 1 => X) = 0) :
    ∃ R0 : Real, ∀ x : M,
      metricScalarAt (I := I) (M := M) g x = R0 := by
  classical
  let scalar : M -> Real := fun y => metricScalarAt (I := I) (M := M) g y
  have hmdiff : MDifferentiable I 𝓘(Real, Real) scalar :=
    (metricScalar_smooth (I := I) (M := M) g).mdifferentiable (by simp)
  have hmf_zero : ∀ x : M, mfderiv I 𝓘(Real, Real) scalar x = 0 := by
    intro x
    ext X
    have hx := hzero x X
    rw [DifferentialGeometry.Integral.Connection.differential1FormFun_apply_eq_extDerivFun] at hx
    rw [DifferentialGeometry.extDerivFun_real_eq_mfderiv] at hx
    simpa [scalar] using hx
  have hloc : IsLocallyConstant scalar :=
    DifferentialGeometry.isLocallyConstant_of_mfderiv_eq_zero (I := I) hmdiff hmf_zero
  by_cases hne : Nonempty M
  · let x0 : M := Classical.choice hne
    refine ⟨scalar x0, ?_⟩
    intro x
    letI : PreconnectedSpace M := inferInstance
    exact hloc.apply_eq_of_preconnectedSpace x x0
  · refine ⟨0, ?_⟩
    intro x
    exact False.elim (hne ⟨x⟩)







omit [SigmaCompactSpace M] in
theorem nablaRic_ein3
    (g : SmoothRiemannianMetric I M)
    (hEin : ∀ x : M, ∀ v w : TangentSpace I x,
      metricRicciAt (I := I) (M := M) g x (DifferentialGeometry.Integral.Connection.vec2 (I := I) v w) =
        (metricScalarAt (I := I) (M := M) g x / 3) * g.inner x v w)
    (x : M) :
    let cov := metricCov (I := I) (M := M) g
    let Ric := metricRicci (I := I) (M := M) g
    let scalar := fun y : M => metricScalarAt (I := I) (M := M) g y
    let nablaRic := totalNabla0SFun (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 2 cov Ric x
    let dScalar := DifferentialGeometry.Integral.Connection.differential1FormFun (I := I) scalar x
    ∀ A B C : TangentSpace I x,
      nablaRic (DifferentialGeometry.Integral.Connection.vec3 (I := I) A B C) =
        (1 / 3 : Real) * dScalar (fun _ : Fin 1 => A) * g.inner x B C := by
  classical
  dsimp
  intro A B C
  let cov := metricCov (I := I) (M := M) g
  let Ric := metricRicci (I := I) (M := M) g
  let scalar := fun y : M => metricScalarAt (I := I) (M := M) g y
  let f3 : M -> Real := fun y : M => (1 / 3 : Real) * scalar y
  let hscalar : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) scalar :=
    metricScalar_smooth (I := I) (M := M) g
  have hf3 : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) f3 := by
    exact contMDiff_const.mul hscalar
  letI := tensor0SBundle_topology (𝕜 := Real) (E := E) (H := H)
    (I := I) (M := M) (s := 1)
  let dScalarSec : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I)
      (M := M) (n := (∞ : WithTop ℕ∞)) 1 :=
    DifferentialGeometry.Integral.Connection.duSec (I := I) scalar hscalar
  let df3 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I)
      (M := M) (n := (∞ : WithTop ℕ∞)) 1 :=
    tensor0SField_smulByFun (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (s := 1)
      (fun _ : M => (1 / 3 : Real)) contMDiff_const dScalarSec
  let metricSec : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I)
      (M := M) (n := (∞ : WithTop ℕ∞)) 2 :=
    metricTensorField (I := I) g
  let smulSec : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I)
      (M := M) (n := (∞ : WithTop ℕ∞)) 2 :=
    tensor0SField_smulByFun (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (s := 2)
      f3 hf3 metricSec
  have hdf3 : ∀ y : M, ∀ v : TangentSpace I y,
      df3 y (fun _ : Fin 1 => v) = extDerivFun (I := I) f3 y v := by
    intro y v
    have hf_y : MDifferentiableAt I 𝓘(Real, Real) scalar y :=
      hscalar.contMDiffAt.mdifferentiableAt (by simp)
    have hconst := DifferentialGeometry.extDerivFun_const_mul
      (I := I) (c := (1 / 3 : Real)) (f := scalar) (x := y) hf_y
    have hv := DFunLike.congr_fun hconst v
    calc
      df3 y (fun _ : Fin 1 => v)
          = (1 / 3 : Real) *
              DifferentialGeometry.Integral.Connection.differential1FormFun (I := I) scalar y
                (fun _ : Fin 1 => v) := by
            simp [df3, dScalarSec]
      _ = (1 / 3 : Real) * extDerivFun (I := I) scalar y v := by
            rw [DifferentialGeometry.Integral.Connection.differential1FormFun_apply_eq_extDerivFun]
       _ = extDerivFun (I := I) f3 y v := by
             simpa [f3, Pi.smul_apply, smul_eq_mul] using hv.symm
  have hRicEq : Ric = smulSec := by
    apply DFunLike.ext
    intro y
    apply ContinuousMultilinearMap.ext
    intro slots
    have hslots : slots = DifferentialGeometry.Integral.Connection.vec2 (I := I) (slots 0) (slots 1) := by
      funext i
      fin_cases i <;> rfl
    have hEin_y := hEin y (slots 0) (slots 1)
    rw [hslots]
    change metricRicciAt (I := I) (M := M) g y
        (DifferentialGeometry.Integral.Connection.vec2 (I := I) (slots 0) (slots 1)) =
      f3 y * metricSec y
        (DifferentialGeometry.Integral.Connection.vec2 (I := I) (slots 0) (slots 1))
    simpa [Ric, smulSec, metricSec, f3, scalar, metricRicci_apply,
      smul_eq_mul, metricTensorField_apply, DifferentialGeometry.Integral.Connection.vec2, div_eq_mul_inv,
      mul_assoc, mul_comm, mul_left_comm] using hEin_y
  letI := tensor0SBundle_topology (𝕜 := Real) (E := E) (H := H)
    (I := I) (M := M) (s := 2)
  letI := tensor0SBundle_fiber (𝕜 := Real) (E := E) (H := H)
    (I := I) (M := M) (s := 2)
  letI := tensor0SBundle_vector (𝕜 := Real) (E := E) (H := H)
    (I := I) (M := M) (s := 2)
  letI := tensor0SBundle_smooth (𝕜 := Real) (E := E) (H := H)
    (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (s := 2)
  let X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
    (ContMDiffSection.exists_eq_at_gen
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x A).choose
  have hX : X x = A :=
    (ContMDiffSection.exists_eq_at_gen
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x A).choose_spec
  let slots : Fin 2 -> TangentSpace I x := DifferentialGeometry.Integral.Connection.vec2 (I := I) B C
  have hreal :=
    nabla_smul_metric (I := I) (M := M) cov g
      (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric_isMetricCompatible (I := I) g)
      f3 hf3 df3 hdf3
  have happly :=
    TotalNabla0SRealizes.apply (I := I) hreal X x slots
  have hsection :=
    totalNabla0SFun_apply_section (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 2 cov X smulSec x slots
  have htot :
      (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
          (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := 1) (q := 2)
          df3 metricSec) x (Fin.cons (X x) slots) =
        totalNabla0SFun (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) 2 cov smulSec x (Fin.cons (X x) slots) := by
    calc
      (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
          (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := 1) (q := 2)
          df3 metricSec) x (Fin.cons (X x) slots)
          =
        nabla0SFun (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) 2 cov X smulSec x slots := by
          simpa [metricSec, smulSec] using happly
      _ =
        totalNabla0SFun (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) 2 cov smulSec x (Fin.cons (X x) slots) := by
          exact hsection.symm
  have hslots3 : Fin.cons A slots = DifferentialGeometry.Integral.Connection.vec3 (I := I) A B C := by
    funext i
    fin_cases i <;> rfl
  have hslots3X : Fin.cons (X x) slots = DifferentialGeometry.Integral.Connection.vec3 (I := I) A B C := by
    rw [hX, hslots3]
  have hprodEval :
      (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
          (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := 1) (q := 2)
          df3 metricSec) x (Fin.cons (X x) slots) =
        (1 / 3 : Real) *
          DifferentialGeometry.Integral.Connection.differential1FormFun (I := I) scalar x
            (fun _ : Fin 1 => A) * g.inner x B C := by
    change (Bundle.continuousMultilinearMap.product_fun
        (df3 x) (metricSec x)) (Fin.cons (X x) slots) =
      (1 / 3 : Real) *
        DifferentialGeometry.Integral.Connection.differential1FormFun (I := I) scalar x
          (fun _ : Fin 1 => A) * g.inner x B C
    rw [Bundle.continuousMultilinearMap.product_fun_apply]
    have hleft :
        Fin.cons (X x) slots ∘ Fin.castAdd 2 =
          fun _ : Fin 1 => A := by
      funext i
      fin_cases i
      exact hX
    have hright :
        Fin.cons (X x) slots ∘ Fin.natAdd 1 = slots := by
      funext i
      fin_cases i <;> rfl
    rw [hleft, hright]
    simp only [df3, tensor0SField_smulByFun_apply]
    change ((1 / 3 : Real) * dScalarSec x (fun _ : Fin 1 => A)) * metricSec x slots = _
    simp [dScalarSec, metricSec, slots, DifferentialGeometry.Integral.Connection.vec2, mul_assoc]
  calc
    totalNabla0SFun (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) 2 cov Ric x (DifferentialGeometry.Integral.Connection.vec3 (I := I) A B C)
        =
      totalNabla0SFun (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) 2 cov smulSec x (DifferentialGeometry.Integral.Connection.vec3 (I := I) A B C) := by
          rw [hRicEq]
    _ =
      (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
          (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := 1) (q := 2)
          df3 metricSec) x (Fin.cons (X x) slots) := by
          rw [← hslots3X, ← htot]
    _ =
      (1 / 3 : Real) *
        DifferentialGeometry.Integral.Connection.differential1FormFun (I := I) scalar x
          (fun _ : Fin 1 => A) * g.inner x B C := hprodEval





theorem dScalar_zero_ein3_at
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {x : M} (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (gInv : Fin 3 -> Fin 3 -> Real)
    (hinv : MetricInverseInBasis_gen (I := I) (M := M) g x basis gInv)
    (hEin : ∀ y : M, ∀ v w : TangentSpace I y,
      metricRicciAt (I := I) (M := M) g y (DifferentialGeometry.Integral.Connection.vec2 (I := I) v w) =
        (metricScalarAt (I := I) (M := M) g y / 3) * g.inner y v w) :
    let scalar := fun y : M => metricScalarAt (I := I) (M := M) g y
    let dScalar := DifferentialGeometry.Integral.Connection.differential1FormFun (I := I) scalar x
    ∀ X : TangentSpace I x, dScalar (fun _ : Fin 1 => X) = 0 := by
  classical
  dsimp
  intro X
  let cov := metricCov (I := I) (M := M) g
  let hcov :=
    DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
      (I := I) (M := M) g
  let Ric : DifferentialGeometry.Integral.Connection.Tensor02Section (I := I) (M := M) :=
    DifferentialGeometry.Integral.Connection.CovariantDerivative.ricciSection (I := I) (M := M) cov hcov
  let scalar : M -> Real :=
    fun y => DifferentialGeometry.Integral.Connection.metricTracePair0SAt (I := I) g (Ric y)
  let nablaRic :=
    totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      2 cov Ric x
  let dScalar := DifferentialGeometry.Integral.Connection.differential1FormFun (I := I) scalar x
  obtain ⟨nablaRm04, hsecond, hRmSymm, hRicTrace, hScalar⟩ :=
    DifferentialGeometry.Integral.Connection.metricBianchiAt (I := I) (M := M) g basis gInv hinv
  have hInv : ∀ i j : Fin 3, gInv i j = gInv j i :=
    invMetric_symm (I := I) (M := M) g x basis gInv hinv
  have hEinNabla : ∀ A B C : TangentSpace I x,
      nablaRic (DifferentialGeometry.Integral.Connection.vec3 (I := I) A B C) =
        (1 / 3 : Real) * dScalar (fun _ : Fin 1 => A) * g.inner x B C := by
    simpa [cov, hcov, Ric, scalar, nablaRic, dScalar, metricCov,
      metricRicci, metricScalarAt] using
      nablaRic_ein3 (I := I) (M := M) g hEin x
  have hNablaSymm : DifferentialGeometry.Integral.Connection.NablaRicSymmAt (I := I) nablaRic := by
    intro A B C
    rw [hEinNabla A B C, hEinNabla A C B]
    rw [g.symm x C B]
  have hcontract :
      DifferentialGeometry.Integral.Connection.ContractedBianchiOfSecondAt (I := I) basis gInv nablaRm04
        nablaRic dScalar :=
    DifferentialGeometry.Integral.Connection.contractOfSecond (I := I) basis gInv nablaRm04
      nablaRic dScalar hRmSymm hRicTrace hScalar hNablaSymm hInv
  have hBianchi : DifferentialGeometry.Integral.Connection.ContractedBianchiAt (I := I) basis gInv nablaRic
      dScalar :=
    DifferentialGeometry.Integral.Connection.contracted_bianchi_of_second (I := I) basis gInv nablaRm04
      nablaRic dScalar hcontract hsecond
  exact DifferentialGeometry.Integral.Connection.dR_zero_nablaEin3 (I := I) (M := M) g basis gInv hinv
    nablaRic dScalar hBianchi hEinNabla X


theorem metricRicciSymm
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis_gen (I := I) g x basis gInv)
    (i j : Idx) :
    metricRicciAt (I := I) (M := M) g x
        (DifferentialGeometry.Integral.Connection.vec2 (I := I) (basis i) (basis j)) =
      metricRicciAt (I := I) (M := M) g x
        (DifferentialGeometry.Integral.Connection.vec2 (I := I) (basis j) (basis i)) := by
  let K := metricCurvData (I := I) (M := M) g
  have hLower :
      DifferentialGeometry.Integral.Connection.Rm04LowersRm13At (I := I) g x
        (metricRm13 (I := I) (M := M) g x)
        (metricRm04 (I := I) (M := M) g x) :=
    DifferentialGeometry.Integral.Connection.rm04LowersRm13At_of_realizes
      (I := I) g (metricCov (I := I) (M := M) g)
      (metricRm13 (I := I) (M := M) g)
      (metricRm04 (I := I) (M := M) g)
      K.h_rm13 K.h_rm04 x
  have hTrace :
      DifferentialGeometry.Integral.Connection.RicciRealizesRm04FirstTraceAt (I := I)
        (metricRicciAt (I := I) (M := M) g x)
        (metricRm04At (I := I) (M := M) g x) gInv basis := by
    have hTrace' :=
      DifferentialGeometry.Integral.Connection.ricciFirstTraceAt_of_rm13_section
        (I := I) g basis gInv hinv
        (metricRicci (I := I) (M := M) g)
        (metricRm13 (I := I) (M := M) g)
        (metricRm04 (I := I) (M := M) g)
        K.h_ricci13 hLower
        (invMetric_symm (I := I) (M := M) g x basis gInv hinv)
    simpa using hTrace'
  have hcov1 :
      CovariantDerivative.ContMDiffCovariantDerivativeLocally
        (I := I) (E := E) (M := M)
        (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) g)
        (1 : WithTop ℕ∞) :=
    DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally_one
      (I := I) (M := M) g
  have hPair :
      ∀ X Y Z W : TangentSpace I x,
        metricRm04At (I := I) (M := M) g x
            (DifferentialGeometry.Integral.Connection.vec4 (I := I) X Y Z W) =
          metricRm04At (I := I) (M := M) g x
            (DifferentialGeometry.Integral.Connection.vec4 (I := I) Z W X Y) := by
    simpa using
      (DifferentialGeometry.Integral.Connection.rm04PairSymmAt_of_leviCivita_realizes
        (I := I) g (metricRm04 (I := I) (M := M) g) K.h_rm04
        (x := x))
  have hOutput :
      DifferentialGeometry.Integral.Connection.Rm04OutputSkewAt (I := I)
        (metricRm04At (I := I) (M := M) g x) := by
    simpa using
      (DifferentialGeometry.Integral.Connection.rm04OutputSkewAt_of_leviCivita_realizes
        (I := I) g (metricRm04 (I := I) (M := M) g) K.h_rm04
        (x := x))
  have hInput :
      ∀ X Y Z W : TangentSpace I x,
        metricRm04At (I := I) (M := M) g x
            (DifferentialGeometry.Integral.Connection.vec4 (I := I) Y X Z W) =
          -metricRm04At (I := I) (M := M) g x
            (DifferentialGeometry.Integral.Connection.vec4 (I := I) X Y Z W) := by
    simpa using
      (DifferentialGeometry.Integral.Connection.rm04InputSkewAt_of_leviCivita_realizes
        (I := I) g (metricRm04 (I := I) (M := M) g) K.h_rm04
        (x := x))
  exact
    DifferentialGeometry.Integral.Connection.ricciSymm_of_rm04 (I := I) basis gInv
      (metricRicciAt (I := I) (M := M) g x)
      (metricRm04At (I := I) (M := M) g x)
      hTrace hPair hOutput hInput
      (invMetric_symm (I := I) (M := M) g x basis gInv hinv) i j



theorem metricNablaSymm
    (g : SmoothRiemannianMetric I M) (x : M) :
    NablaRicSymmAt (I := I)
      (totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 (metricCov (I := I) (M := M) g) (metricRicci (I := I) (M := M) g) x) := by
  classical
  intro A B C
  obtain ⟨X, hX⟩ :=
    ContMDiffSection.exists_eq_at_gen
      (I := I) (F := E) (V := TangentSpace I)
      (n := (⊤ : ℕ∞)) x A
  have hRicSymm :
      ∀ y : M, ∀ U V : TangentSpace I y,
        metricRicci (I := I) (M := M) g y
            (fun q : Fin 2 => if q = 0 then U else V) =
          metricRicci (I := I) (M := M) g y
            (fun q : Fin 2 => if q = 0 then V else U) := by
    intro y U V
    let basis := DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis
      (I := I) y
    let gInv : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E →
        DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E → Real :=
      fun i j =>
        DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_component
          (I := I) g y i j (extChartAt I y y)
    have hinv : MetricInverseInBasis_gen (I := I) (M := M) g y basis gInv := by
      simpa [basis, gInv] using
        (DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_metricInverseInBasis_center
          (I := I) g y)
    have hcomp :
        ∀ i j : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
          metricRicci (I := I) (M := M) g y
              (fun q : Fin 2 => if q = 0 then basis i else basis j) =
            metricRicci (I := I) (M := M) g y
              (fun q : Fin 2 => if q = 0 then basis j else basis i) := by
      intro i j
      simpa [basis, metricRicci_apply,
        DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis_apply] using
        (metricRicciSymm (I := I) (M := M) g basis gInv hinv i j)
    exact
      DifferentialGeometry.Tensor.Coordinates.tensor0S_two_symm_of_coordFrame
        (I := I) basis (metricRicci (I := I) (M := M) g y) hcomp U V
  have hsymm :=
    DifferentialGeometry.Tensor.Coordinates.nabla0SFun_two_symm_of_symm
      (I := I) (metricCov (I := I) (M := M) g) X
      (metricRicci (I := I) (M := M) g) x hRicSymm B C
  have hleft :=
    totalNabla0SFun_apply_section
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      2 (metricCov (I := I) (M := M) g) X
      (metricRicci (I := I) (M := M) g) x (vec2 (I := I) B C)
  have hright :=
    totalNabla0SFun_apply_section
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      2 (metricCov (I := I) (M := M) g) X
      (metricRicci (I := I) (M := M) g) x (vec2 (I := I) C B)
  rw [← hX]
  rw [show vec3 (I := I) (X x) B C = Fin.cons (X x) (vec2 (I := I) B C) by
    ext q
    fin_cases q <;> rfl]
  rw [show vec3 (I := I) (X x) C B = Fin.cons (X x) (vec2 (I := I) C B) by
    ext q
    fin_cases q <;> rfl]
  rw [hleft, hright]
  exact hsymm






theorem metricRicci_velocity_eq_sum_rm04_frame
    (g : SmoothRiemannianMetric I M) {m : Nat} {x : M}
    (basis : Module.Basis (Fin (m + 1)) Real (TangentSpace I x))
    (hON : forall a b,
      g.inner x (basis a) (basis b) = if a = b then 1 else 0)
    {T : TangentSpace I x} {E : Fin m -> TangentSpace I x}
    (h0 : basis 0 = T)
    (hSucc : forall i : Fin m, basis i.succ = E i) :
    metricRicci (I := I) (M := M) g x (vec2 (I := I) T T) =
      ∑ i, metricRm04StdAt (I := I) (M := M) g x (E i) T T (E i) := by
  classical
  let K := metricCurvData (I := I) (M := M) g
  have hLower :
      DifferentialGeometry.Integral.Connection.Rm04LowersRm13At (I := I) g x
        (metricRm13 (I := I) (M := M) g x)
        (metricRm04 (I := I) (M := M) g x) :=
    DifferentialGeometry.Integral.Connection.rm04LowersRm13At_of_realizes
      (I := I) g (metricCov (I := I) (M := M) g)
      (metricRm13 (I := I) (M := M) g)
      (metricRm04 (I := I) (M := M) g)
      K.h_rm13 K.h_rm04 x
  have hTrace :=
    DifferentialGeometry.Integral.Connection.ricci_diag_eq_sum_rm04_diag_of_orthonormal
      (I := I) (M := M) (Idx := Fin (m + 1)) g basis
      (metricRicci (I := I) (M := M) g)
      (metricRm13 (I := I) (M := M) g)
      (metricRm04 (I := I) (M := M) g)
      K.h_ricci13 hLower hON
      (0 : Fin (m + 1)) (0 : Fin (m + 1))
  have hTraceSplit :
      metricRicci (I := I) (M := M) g x
          (DifferentialGeometry.Integral.Connection.vec2 (I := I) (basis 0) (basis 0)) =
        metricRm04 (I := I) (M := M) g x
            (DifferentialGeometry.Integral.Connection.vec4 (I := I) (basis 0) (basis 0) (basis 0) (basis 0)) +
          ∑ i : Fin m,
            metricRm04 (I := I) (M := M) g x
              (DifferentialGeometry.Integral.Connection.vec4 (I := I)
                (basis i.succ) (basis 0) (basis 0) (basis i.succ)) := by
    simpa [Fin.sum_univ_succ] using hTrace
  have hInput :
      forall X Y Z W : TangentSpace I x,
        metricRm04At (I := I) (M := M) g x
            (DifferentialGeometry.Integral.Connection.vec4 (I := I) Y X Z W) =
          -metricRm04At (I := I) (M := M) g x
            (DifferentialGeometry.Integral.Connection.vec4 (I := I) X Y Z W) := by
    simpa using
      (DifferentialGeometry.Integral.Connection.rm04InputSkewAt_of_leviCivita_realizes
        (I := I) g (metricRm04 (I := I) (M := M) g) K.h_rm04
        (x := x))
  have hzero :
      metricRm04 (I := I) (M := M) g x
          (DifferentialGeometry.Integral.Connection.vec4 (I := I) (basis 0) (basis 0) (basis 0) (basis 0)) =
        0 := by
    have hself :
        metricRm04At (I := I) (M := M) g x
            (DifferentialGeometry.Integral.Connection.vec4 (I := I) (basis 0) (basis 0) (basis 0) (basis 0)) =
          -metricRm04At (I := I) (M := M) g x
            (DifferentialGeometry.Integral.Connection.vec4 (I := I) (basis 0) (basis 0) (basis 0) (basis 0)) :=
      hInput (basis 0) (basis 0) (basis 0) (basis 0)
    have hzeroAt :
        metricRm04At (I := I) (M := M) g x
            (DifferentialGeometry.Integral.Connection.vec4 (I := I) (basis 0) (basis 0) (basis 0) (basis 0)) =
          0 := by
      linarith
    simpa [metricRm04_apply] using hzeroAt
  have hTail := hTraceSplit
  rw [hzero, zero_add] at hTail
  simpa [h0, hSucc, metricRm04_apply, metricRm04StdAt_apply,
    vec2, vec4, DifferentialGeometry.Integral.Connection.vec2, DifferentialGeometry.Integral.Connection.vec4] using hTail



theorem metricRicci_velocity_eq_sum_inner_curv_frame
    (g : SmoothRiemannianMetric I M) {m : Nat} {x : M}
    (basis : Module.Basis (Fin (m + 1)) Real (TangentSpace I x))
    (hON : forall a b,
      g.inner x (basis a) (basis b) = if a = b then 1 else 0)
    {T : TangentSpace I x} {E : Fin m -> TangentSpace I x}
    (h0 : basis 0 = T)
    (hSucc : forall i : Fin m, basis i.succ = E i) :
    metricRicci (I := I) (M := M) g x (vec2 (I := I) T T) =
      ∑ i, g.inner x
        (DifferentialGeometry.Integral.Connection.metricSharp (I := I) g x
          (metricRm04LastDualAt (I := I) (M := M) g x (E i) T T))
        (E i) := by
  rw [metricRicci_velocity_eq_sum_rm04_frame
    (I := I) (M := M) g basis hON h0 hSucc]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [DifferentialGeometry.Integral.Connection.inner_metricSharp]
  rfl

end DifferentialGeometry.Integral.Connection
