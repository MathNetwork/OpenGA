import DifferentialGeometry.Geometry.Operator.HessianTraceRealization
import DifferentialGeometry.Geometry.Operator.RoughLaplacian
import DifferentialGeometry.Geometry.Curvature.Components.Basic
import DifferentialGeometry.Geometry.Curvature.Components.Lowering
import DifferentialGeometry.Geometry.Curvature.Components.TraceOneForm
import DifferentialGeometry.Geometry.Curvature.Components.RicciTrace
import DifferentialGeometry.Geometry.Curvature.Components.LocalFrame
import DifferentialGeometry.Geometry.Curvature.Components.Christoffel
import DifferentialGeometry.Geometry.Curvature.Components.RicciIdentity
import DifferentialGeometry.Tensor.RicciIdentity.OneForm
import DifferentialGeometry.Tensor.RicciIdentity.Tensor0S.Realization
import DifferentialGeometry.Tensor.RicciIdentity.Tensor0S.Formula
import DifferentialGeometry.Tensor.RicciIdentity.MixedComponents
import DifferentialGeometry.Geometry.Connection.LeviCivita.KoszulFormula
import DifferentialGeometry.Geometry.Coordinates.CoordinateFrame
import DifferentialGeometry.Tensor.RSTensor.CoordinateBasis
import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.HigherOrder
import DifferentialGeometry.Tensor.RSTensor.Tensor0SRiemannian.Basic
import DifferentialGeometry.Tensor.RSTensor.Tensor0SRiemannian.Coordinate
import DifferentialGeometry.Tensor.RSTensor.Tensor0SRiemannian.Comparison
import DifferentialGeometry.Tensor.RSTensor.Tensor0SRiemannian.Product
import DifferentialGeometry.Tensor.RSTensor.Tensor0SRiemannian.Smooth
import DifferentialGeometry.Tensor.RSTensor.MetricCompatibility

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false














noncomputable section

namespace DifferentialGeometry.Integral.Connection

open Bundle Tensor0SBundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]


def gradNormSq (g : SmoothRiemannianMetric I M) (u : M -> Real) : M -> Real :=
  fun x => g.inner x (gradientFun (I := I) g u x) (gradientFun (I := I) g u x)


def hessianNormSq
    (g : SmoothRiemannianMetric I M)
    (Hess : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :
    M -> Real :=
  fun x => normSq0S (I := I) g x 2 (Hess x)


def ricciGradGrad
    (Ric : Tensor02Section (I := I) (M := M))
    (g : SmoothRiemannianMetric I M) (u : M -> Real) : M -> Real :=
  fun x => Ric x (vec2 (gradientFun (I := I) g u x) (gradientFun (I := I) g u x))





private theorem cotangentInner_eq_gen
    (g : SmoothRiemannianMetric I M) (x : M)
    (α β : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x) :
    Tensor0SBundle.cotangentInner (I := I) g x α β =
      cotangentInner_gen (I := I) g x α β := rfl


theorem cotangentSharp_differential1FormFun_eq_gradientFun
    (g : SmoothRiemannianMetric I M) (u : M -> Real) (x : M) :
    cotangentSharp_gen (I := I) g x (differential1FormFun (I := I) u x) =
      gradientFun (I := I) g u x := by
  apply (metricFlatEquiv (I := I) g x).injective
  ext X
  change
    g.inner x (cotangentSharp_gen (I := I) g x (differential1FormFun (I := I) u x)) X =
      g.inner x (gradientFun (I := I) g u x) X
  rw [cotangentSharp_inner_gen, inner_gradientFun]
  rfl


theorem inner0S_differential1FormFun_pair_eq_grad_inner
    (g : SmoothRiemannianMetric I M) (u v : M -> Real) (x : M) :
    inner0S (I := I) g x 1
        (differential1FormFun (I := I) u x)
        (differential1FormFun (I := I) v x) =
      g.inner x (gradientFun (I := I) g u x) (gradientFun (I := I) g v x) := by
  rw [Tensor0SBundle.inner0S_one_eq_cotangent, cotangentInner_eq_gen,
    cotangentInner_eq_sharp_gen]
  rw [cotangentSharp_differential1FormFun_eq_gradientFun,
    cotangentSharp_differential1FormFun_eq_gradientFun]



theorem inner0S_one_eq_eval_sharp_right
    (g : SmoothRiemannianMetric I M) (x : M)
    (α β : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x) :
    inner0S (I := I) g x 1 α β =
      cotangentToDual_gen (I := I) α (cotangentSharp_gen (I := I) g x β) := by
  rw [Tensor0SBundle.inner0S_one_eq_cotangent, cotangentInner_eq_gen,
    cotangentInner_eq_sharp_gen, cotangentSharp_inner_gen]


theorem inner0S_differential1FormFun_eq_gradNormSq
    (g : SmoothRiemannianMetric I M) (u : M -> Real) (x : M) :
    inner0S (I := I) g x 1
        (differential1FormFun (I := I) u x)
        (differential1FormFun (I := I) u x) =
      gradNormSq (I := I) g u x := by
  rw [inner0S_differential1FormFun_pair_eq_grad_inner]
  rfl









def OneFormNormBochnerAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    (α roughAlpha : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (nablaAlpha : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (x : M) : Prop :=
  (1 / 2 : Real) *
      laplacian (I := I) cov g
        (fun y : M => inner0S (I := I) g y 1 (α y) (α y)) x =
    inner0S (I := I) g x 1 (roughAlpha x) (α x) +
      normSq0S (I := I) g x 2 (nablaAlpha x)






def DifferentialOneFormCommutatorAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    (Ric : Tensor02Section (I := I) (M := M))
    (u : M -> Real)
    (roughDu : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (x : M) : Prop :=
  inner0S (I := I) g x 1 (roughDu x) (differential1FormFun (I := I) u x) =
    inner0S (I := I) g x 1
        (differential1FormFun (I := I) (laplacian (I := I) cov g u) x)
        (differential1FormFun (I := I) u x) +
      ricciGradGrad (I := I) Ric g u x



def OneFormCommutatorEvalAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    (Ric : Tensor02Section (I := I) (M := M))
    (u : M -> Real)
    (roughDu : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (x : M) : Prop :=
  ∀ Y : TangentSpace I x,
    roughDu x (fun _ : Fin 1 => Y) =
      differential1FormFun (I := I) (laplacian (I := I) cov g u) x
          (fun _ : Fin 1 => Y) +
        Ric x (vec2 Y (gradientFun (I := I) g u x))



def traceNablaHessianForDLap
    (g : SmoothRiemannianMetric I M)
    {x : M}
    (nabla2Du :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (Y : TangentSpace I x) : Real :=
  metricTraceLastTwo0SAt3 (I := I) g nabla2Du Y


def traceNablaHessianForDLapInBasis
    {Idx : Type*} [Fintype Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (nabla2Du :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (Y : TangentSpace I x) : Real :=
  traceNablaOneFormAt (I := I) basis gInv nabla2Du Y


def TraceNablaHessianRealizesDLapAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    {x : M}
    (u : M -> Real)
    (nabla2Du :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x) :
    Prop :=
  ∀ Y : TangentSpace I x,
    traceNablaHessianForDLap (I := I) g nabla2Du Y =
      differential1FormFun (I := I) (laplacian (I := I) cov g u) x
        (fun _ : Fin 1 => Y)



def TraceNablaHessianRealizesDLapAtInBasis
    {Idx : Type*} [Fintype Idx]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (u : M -> Real)
    (nabla2Du :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x) :
    Prop :=
  ∀ Y : TangentSpace I x,
    traceNablaHessianForDLapInBasis (I := I) basis gInv nabla2Du Y =
      differential1FormFun (I := I) (laplacian (I := I) cov g u) x
        (fun _ : Fin 1 => Y)



theorem TraceNablaHessianRealizesDLapAt.toInBasis
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis_gen (I := I) g x basis gInv)
    (u : M -> Real)
    (nabla2Du :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (h : TraceNablaHessianRealizesDLapAt (I := I) cov g u nabla2Du) :
    TraceNablaHessianRealizesDLapAtInBasis (I := I) cov g basis gInv u nabla2Du := by
  intro Y
  unfold traceNablaHessianForDLapInBasis traceNablaOneFormAt
  rw [← h Y]
  unfold traceNablaHessianForDLap
  exact (metricTraceLastTwo0SAt3_eq_sum_basis (I := I) g basis gInv hinv
    nabla2Du Y).symm

private theorem metricTensorField_eq_metricTensor0S
    (g : SmoothRiemannianMetric I M) (x : M) :
    metricTensorField (I := I) g x = metricTensor0S (I := I) g x := by
  classical
  let basis : Module.Basis (Fin (Module.finrank Real (TangentSpace I x))) Real
      (TangentSpace I x) :=
    Module.finBasis Real (TangentSpace I x)
  apply ext0S_basis (I := I) basis
  intro slots
  simp [component0S_apply]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
private theorem fin_cons_vec2_eq_vec3_local {x : M}
    (X Y Z : TangentSpace I x) :
    Fin.cons X (vec2 (I := I) Y Z) = vec3 (I := I) X Y Z := by
  funext a
  fin_cases a <;> rfl

omit [FiniteDimensional ℝ E] in
private theorem curry_three_apply_vec2 {x : M}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (X Y Z : TangentSpace I x) :
    tensor0S_curry (I := I) (𝕜 := Real) (M := M) 2 x T X
        (vec2 (I := I) Y Z) =
      T (vec3 (I := I) X Y Z) := by
  change
    (((continuousMultilinearCurryLeftEquiv Real
        (fun _ : Fin 3 => E) Real)
        ((tensor0SSpace_continuousLinearEquiv (I := I) (M := M) 3 x) T)
        X)
        (vec2 (I := I) Y Z)) =
      ((tensor0SSpace_continuousLinearEquiv (I := I) (M := M) 3 x) T)
        (vec3 (I := I) X Y Z)
  rw [continuousMultilinearCurryLeftEquiv_apply]
  congr 1
  exact fin_cons_vec2_eq_vec3_local (I := I) X Y Z

private theorem freezeLastTwo0S3_eq_curry {x : M}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (X : TangentSpace I x) :
    freezeLastTwo0S3 (I := I) T X =
      tensor0S_curry (I := I) (𝕜 := Real) (M := M) 2 x T X := by
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
  rw [hslots, freezeLastTwo0S3_apply, curry_three_apply_vec2]







theorem extDeriv_metricTrace_eq_traceNabla
    [T2Space M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    (hmc : DifferentialGeometry.Integral.Connection.IsMetricCompatible_gen (I := I) cov g)
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2)
    (nablaA :
      Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) 3)
    (hA : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I)
      (M := M) 2 cov A nablaA)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (x : M) :
    extDerivFun (I := I)
        (fun y : M => metricTracePair0SAt (I := I) g (A y)) x (X x) =
      metricTraceLastTwo0SAt3 (I := I) g (nablaA x) (X x) := by
  classical
  have hinner := Tensor0SBundle.inner0S_two_nabla
    (I := I) cov g hmc (metricTensorField (I := I) g) A X x
  have hfun :
      (fun y : M =>
          inner0S (I := I) g y 2 (metricTensorField (I := I) g y) (A y)) =
        fun y : M => metricTracePair0SAt (I := I) g (A y) := by
    funext y
    rw [metricTracePair0SAt, metricTensorField_eq_metricTensor0S]
  have htrace :
      inner0S (I := I) g x 2 (metricTensorField (I := I) g x)
          (tensor0S_curry (I := I) (𝕜 := Real) (M := M) 2 x (nablaA x) (X x)) =
        metricTraceLastTwo0SAt3 (I := I) g (nablaA x) (X x) := by
    rw [metricTensorField_eq_metricTensor0S, metricTraceLastTwo0SAt3,
      metricTracePair0SAt, freezeLastTwo0S3_eq_curry]
  have hnabla :
      nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          2 cov X A x =
        tensor0S_curry (I := I) (𝕜 := Real) (M := M) 2 x (nablaA x) (X x) := by
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
    rw [hslots, curry_three_apply_vec2]
    rw [← fin_cons_vec2_eq_vec3_local]
    exact (hA X x (vec2 (I := I) (basis (slots 0)) (basis (slots 1)))).symm
  have hmetricZero := nabla_metric_zero (I := I) cov g hmc X x
  rw [hfun] at hinner
  rw [hmetricZero, hnabla] at hinner
  rw [htrace] at hinner
  have hzeroInner :
      inner0S (I := I) g x 2
          (0 : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            2 x)
          (A x) = 0 := by
    change
      (tensor0SMetricData (I := I) g x 2).flat
        (0 : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          2 x) (A x) = 0
    have hflat :
        (tensor0SMetricData (I := I) g x 2).flat
          (0 : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            2 x) = 0 := by
      exact LinearMap.map_zero
        ((tensor0SMetricData (I := I) g x 2).flat.toLinearMap :
          Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            2 x →ₗ[Real]
          Module.Dual Real
            (Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
              2 x))
    rw [hflat]
    rfl
  rw [hzeroInner, zero_add] at hinner
  simpa using hinner








theorem traceNablaHessianRealizesDLapAt_of_lapTrace
    [T2Space M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    (hmc : DifferentialGeometry.Integral.Connection.IsMetricCompatible_gen (I := I) cov g)
    (u : M -> Real)
    (nablaDuSec : TwoTensorSection (I := I) (M := M))
    (nabla2DuSec :
      Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) 3)
    (hnabla : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I)
      (M := M) 2 cov nablaDuSec nabla2DuSec)
    (hlap : ∀ y : M,
      laplacian (I := I) cov g u y =
        scalarLapTraceAt (I := I) g (nablaDuSec y))
    (x : M) :
    TraceNablaHessianRealizesDLapAt (I := I) cov g u (nabla2DuSec x) := by
  intro Y
  obtain ⟨X, hX⟩ :=
    ContMDiffSection.exists_eq_at_gen
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x Y
  have htrace := extDeriv_metricTrace_eq_traceNabla
    (I := I) cov g hmc nablaDuSec nabla2DuSec hnabla X x
  have hfun :
      (fun y : M => laplacian (I := I) cov g u y) =
        fun y : M => metricTracePair0SAt (I := I) g (nablaDuSec y) := by
    funext y
    rw [hlap y, scalarLapTraceAt]
  rw [differential1FormFun_apply_eq_extDerivFun]
  change traceNablaHessianForDLap (I := I) g (nabla2DuSec x) Y =
    extDerivFun (I := I) (fun y : M => laplacian (I := I) cov g u y) x Y
  rw [hfun]
  simpa [hX] using htrace.symm



theorem lapTrace_eq_direct
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    (u : M -> Real)
    (Hess : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (htrace : ∀ y : M,
      ScalarLaplacianRealizesTraceAt (I := I) cov g u (Hess y)) :
    ∀ y : M,
      laplacian (I := I) cov g u y =
        scalarLapTraceAt (I := I) g (Hess y) := by
  intro y
  exact ScalarLaplacianRealizesTraceAt.eq_trace (I := I) cov g u (Hess y) (htrace y)



theorem lapTrace_eq_pair_of_traceAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    (u : M -> Real)
    (Hess : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (htrace : ∀ y : M,
      ScalarLaplacianRealizesTraceAt (I := I) cov g u (Hess y)) :
    ∀ y : M,
      laplacian (I := I) cov g u y =
        metricTracePair0SAt (I := I) g (Hess y) := by
  intro y
  rw [lapTrace_eq_direct (I := I) cov g u Hess htrace y, scalarLapTraceAt]



theorem traceNablaHessianRealizesDLapAt_of_traceAt
    [T2Space M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    (hmc : DifferentialGeometry.Integral.Connection.IsMetricCompatible_gen (I := I) cov g)
    (u : M -> Real)
    (nablaDuSec : TwoTensorSection (I := I) (M := M))
    (nabla2DuSec :
      Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) 3)
    (hnabla : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I)
      (M := M) 2 cov nablaDuSec nabla2DuSec)
    (htrace : ∀ y : M,
      ScalarLaplacianRealizesTraceAt (I := I) cov g u (nablaDuSec y))
    (x : M) :
    TraceNablaHessianRealizesDLapAt (I := I) cov g u (nabla2DuSec x) :=
  traceNablaHessianRealizesDLapAt_of_lapTrace (I := I) cov g hmc u
    nablaDuSec nabla2DuSec hnabla
    (lapTrace_eq_direct (I := I) cov g u nablaDuSec htrace) x



def OneFormRicciTraceCommAt
    {Idx : Type*} [Fintype Idx]
    (g : SmoothRiemannianMetric I M)
    (Ric : Tensor02Section (I := I) (M := M))
    (u : M -> Real)
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (nabla2Du :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x) :
    Prop :=
  OneFormRicciTraceCommWithVectorAt (I := I) Ric basis gInv
    (gradientFun (I := I) g u x) nabla2Du





def oneFormRicciTraceComm_coordAt
    (g : SmoothRiemannianMetric I M)
    (Ric : Tensor02Section (I := I) (M := M))
    (u : M -> Real)
    (x₀ : M)
    (gInv : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E -> DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E -> Real)
    (nabla2Du :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x₀) :
    Prop :=
  OneFormRicciTraceCommAt (I := I) g Ric u
    (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis (I := I) x₀) gInv nabla2Du

theorem oneFormRicciTraceComm_coordAt_iff
    (g : SmoothRiemannianMetric I M)
    (Ric : Tensor02Section (I := I) (M := M))
    (u : M -> Real)
    (x₀ : M)
    (gInv : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E -> DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E -> Real)
    (nabla2Du :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x₀) :
    oneFormRicciTraceComm_coordAt (I := I) g Ric u x₀ gInv nabla2Du ↔
      OneFormRicciTraceCommAt (I := I) g Ric u
        (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis (I := I) x₀) gInv nabla2Du :=
  Iff.rfl







def curvatureTraceDuAt
    {Idx : Type*} [Fintype Idx]
    (Rm13 : Tensor13Section (I := I) (M := M))
    (u : M -> Real)
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (Y : TangentSpace I x) : Real :=
  curvatureTraceOneFormAt (I := I) Rm13
    (differential1FormFun (I := I) u x) basis gInv Y



def CurvatureTraceDuEqRicciGradAt
    {Idx : Type*} [Fintype Idx]
    (g : SmoothRiemannianMetric I M)
    (Ric : Tensor02Section (I := I) (M := M))
    (Rm13 : Tensor13Section (I := I) (M := M))
    (u : M -> Real)
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real) : Prop :=
  CurvatureTraceOneFormEqRicVectorAt (I := I) Ric Rm13
    (differential1FormFun (I := I) u x) basis gInv
    (gradientFun (I := I) g u x)


theorem differential1FormFun_eq_metric_dual_gradientFun
    (g : SmoothRiemannianMetric I M) (u : M -> Real) (x : M) :
    differential1FormFun (I := I) u x =
      dualToCotangent_gen (I := I)
        ((tangentFlatLinear_gen (I := I) g x) (gradientFun (I := I) g u x)) := by
  apply cotangentToDualLinear_injective_gen (I := I) (x := x)
  ext V
  simp only [cotangentToDualLinear_apply_gen, cotangentToDual_apply_gen, gradientFun_eq, metricSharp_eq,
    cotangentToDual_dualToCotangent_gen, tangentFlatLinear_apply_gen]
  exact (inner_gradientFun (I := I) g u x V).symm




theorem curvatureTraceDuEqRicciGradAt_of_metric_dual
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M)
    (Ric : Tensor02Section (I := I) (M := M))
    (Rm13 : Tensor13Section (I := I) (M := M))
    (u : M -> Real)
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis_gen (I := I) g x basis gInv)
    (hRic : RicciTensorRealizesRm13Trace (I := I) Ric Rm13)
    (hSkew : Rm13MetricSkewAt (I := I) g x (Rm13 x)) :
    CurvatureTraceDuEqRicciGradAt (I := I) g Ric Rm13 u basis gInv := by
  exact curvatureTraceOneFormEqRicVectorAt_of_metric_dual (I := I) g Ric Rm13
    (differential1FormFun (I := I) u x) basis gInv
    (gradientFun (I := I) g u x) hinv hRic hSkew
    (differential1FormFun_eq_metric_dual_gradientFun (I := I) g u x)



def nabla2DuCoord
    {Idx : Type*}
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (nabla2Du :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (i j k : Idx) : Real :=
  nabla2OneFormCoord (I := I) basis nabla2Du i j k




def curvatureActionOnDuCoord
    {Idx : Type*}
    (Rm13 : Tensor13Section (I := I) (M := M))
    (u : M -> Real)
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (i k j : Idx) : Real :=
  curvatureActionOnOneFormCoord (I := I) Rm13
    (differential1FormFun (I := I) u x) basis i k j


def ricGradCoord
    {Idx : Type*}
    (g : SmoothRiemannianMetric I M)
    (Ric : Tensor02Section (I := I) (M := M))
    (u : M -> Real)
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (k : Idx) : Real :=
  ricciVectorCoord (I := I) Ric basis (gradientFun (I := I) g u x) k

omit [FiniteDimensional ℝ E] in
theorem nabla2DuTrailingSymmCoord_of_tensor
    {Idx : Type*}
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (nabla2Du :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (hsymm : OneFormLastTwoSymmAt (I := I) nabla2Du) :
    Nabla2DuTrailingSymmCoord (nabla2DuCoord (I := I) basis nabla2Du) := by
  simpa [nabla2DuCoord] using
    nabla2OneFormTrailingSymmCoord_of_tensor (I := I) basis nabla2Du hsymm

theorem curvatureActionTraceEqualsRicGradCoord_of_tensor
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M)
    (Ric : Tensor02Section (I := I) (M := M))
    (Rm13 : Tensor13Section (I := I) (M := M))
    (u : M -> Real)
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hcurv : CurvatureTraceDuEqRicciGradAt (I := I) g Ric Rm13 u basis gInv) :
    CurvatureActionTraceEqualsRicGradCoord gInv
      (curvatureActionOnDuCoord (I := I) Rm13 u basis)
      (ricGradCoord (I := I) g Ric u basis) := by
  simpa [curvatureActionOnDuCoord, ricGradCoord, CurvatureTraceDuEqRicciGradAt] using
    curvatureActionTraceEqualsRicVectorCoord_of_tensor (I := I) Ric Rm13
      (differential1FormFun (I := I) u x) basis gInv
      (gradientFun (I := I) g u x) hcurv






theorem oneFormRicciTraceComm_coordAt_of_third_comm
    (g : SmoothRiemannianMetric I M)
    (Ric : Tensor02Section (I := I) (M := M))
    (Rm13 : Tensor13Section (I := I) (M := M))
    (u : M -> Real)
    (x₀ : M)
    (gInv : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E -> DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E -> Real)
    (nabla2Du :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x₀)
    (hsymm : OneFormLastTwoSymmAt (I := I) nabla2Du)
    (hcomm : OneFormThirdCovDerivCommAt (I := I) Rm13
      (differential1FormFun (I := I) u x₀) nabla2Du)
    (hcurv : CurvatureTraceDuEqRicciGradAt (I := I) g Ric Rm13 u
      (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis (I := I) x₀) gInv) :
    oneFormRicciTraceComm_coordAt (I := I) g Ric u x₀ gInv nabla2Du := by
  rw [oneFormRicciTraceComm_coordAt_iff]
  simpa [OneFormRicciTraceCommAt, CurvatureTraceDuEqRicciGradAt, curvatureTraceDuAt] using
    oneForm_ricci_trace_comm_of_third_comm (I := I) Ric Rm13
      (differential1FormFun (I := I) u x₀)
      (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis (I := I) x₀) gInv
      (gradientFun (I := I) g u x₀) nabla2Du hsymm hcomm
      (by
        intro Y
        simpa [CurvatureTraceDuEqRicciGradAt, curvatureTraceDuAt,
          curvatureTraceOneFormAt] using hcurv Y)



theorem oneForm_commutator_pair_of_eval
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    (Ric : Tensor02Section (I := I) (M := M))
    (u : M -> Real)
    (roughDu : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (x : M)
    (hcomm : OneFormCommutatorEvalAt (I := I) cov g Ric u roughDu x) :
    DifferentialOneFormCommutatorAt (I := I) cov g Ric u roughDu x := by
  unfold DifferentialOneFormCommutatorAt
  rw [inner0S_one_eq_eval_sharp_right (I := I) g x
    (roughDu x) (differential1FormFun (I := I) u x)]
  rw [inner0S_one_eq_eval_sharp_right (I := I) g x
    (differential1FormFun (I := I) (laplacian (I := I) cov g u) x)
    (differential1FormFun (I := I) u x)]
  rw [cotangentSharp_differential1FormFun_eq_gradientFun]
  simpa [OneFormCommutatorEvalAt, ricciGradGrad, cotangentToDual_apply_gen] using
    hcomm (gradientFun (I := I) g u x)



def HessianNormRealizesNablaDifferentialAt
    (g : SmoothRiemannianMetric I M)
    (Hess nablaDu : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (x : M) : Prop :=
  normSq0S (I := I) g x 2 (nablaDu x) =
    hessianNormSq (I := I) g Hess x


def oneFormRoughInnerCoord
    {Idx : Type*} [Fintype Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (αx : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (nabla2Alpha : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      3 x) : Real :=
  ∑ i : Idx, ∑ j : Idx,
    gInv i j * roughLap1FormAt (I := I) basis gInv nabla2Alpha (basis i) *
      αx (fun _ : Fin 1 => basis j)


def oneFormNablaNormCoord
    {Idx : Type*} [Fintype Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (nablaAlphaX :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :
    Real :=
  ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
    gInv i k * gInv j l *
      nablaAlphaX (vec2 (basis i) (basis j)) *
        nablaAlphaX (vec2 (basis k) (basis l))




def OneFormNormSecondProductInBasis
    {Idx : Type*} [Fintype Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (alphaX : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (nablaAlphaX :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (normSecond :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :
    Prop :=
  ∀ i j : Idx,
    gInv i j *
        normSecond (metricTraceInput (I := I) (basis i) (basis j) Fin.elim0) =
      (2 : Real) *
        (gInv i j * roughLap1FormAt (I := I) basis gInv nabla2Alpha (basis i) *
            alphaX (fun _ : Fin 1 => basis j) +
          ∑ k : Idx, ∑ l : Idx,
            gInv i k * gInv j l *
              nablaAlphaX (vec2 (basis i) (basis j)) *
                nablaAlphaX (vec2 (basis k) (basis l)))






def MetricTraceInnerProductRuleAt
    {Idx : Type*} [Fintype Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (alphaX : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (nablaAlphaX :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (normSecond :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :
    Prop :=
  metricTrace0S2InBasis (I := I) basis gInv normSecond Fin.elim0 =
    (2 : Real) *
      (oneFormRoughInnerCoord (I := I) basis gInv alphaX nabla2Alpha +
        oneFormNablaNormCoord (I := I) basis gInv nablaAlphaX)

omit [FiniteDimensional ℝ E] in
theorem metricTrace_inner_product_rule
    {Idx : Type*} [Fintype Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (alphaX : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (nablaAlphaX :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (normSecond :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (h : MetricTraceInnerProductRuleAt (I := I) basis gInv alphaX nablaAlphaX
      nabla2Alpha normSecond) :
    metricTrace0S2InBasis (I := I) basis gInv normSecond Fin.elim0 =
      (2 : Real) *
        (oneFormRoughInnerCoord (I := I) basis gInv alphaX nabla2Alpha +
          oneFormNablaNormCoord (I := I) basis gInv nablaAlphaX) :=
  h



omit [FiniteDimensional ℝ E] in
theorem metricTrace_inner_product_rule_of_second_product
    {Idx : Type*} [Fintype Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (alphaX : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (nablaAlphaX :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (normSecond :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (hprod : OneFormNormSecondProductInBasis (I := I) basis gInv alphaX
      nablaAlphaX nabla2Alpha normSecond) :
    MetricTraceInnerProductRuleAt (I := I) basis gInv alphaX nablaAlphaX
      nabla2Alpha normSecond := by
  classical
  unfold MetricTraceInnerProductRuleAt metricTrace0S2InBasis
    oneFormRoughInnerCoord oneFormNablaNormCoord
  calc
    (∑ i : Idx, ∑ j : Idx,
        gInv i j *
          normSecond (metricTraceInput (I := I) (basis i) (basis j) Fin.elim0))
        =
      ∑ i : Idx, ∑ j : Idx,
        (2 : Real) *
          (gInv i j * roughLap1FormAt (I := I) basis gInv nabla2Alpha (basis i) *
              alphaX (fun _ : Fin 1 => basis j) +
            ∑ k : Idx, ∑ l : Idx,
              gInv i k * gInv j l *
                nablaAlphaX (vec2 (basis i) (basis j)) *
                  nablaAlphaX (vec2 (basis k) (basis l))) := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          exact hprod i j
    _ =
      (2 : Real) *
        ((∑ i : Idx, ∑ j : Idx,
            gInv i j * roughLap1FormAt (I := I) basis gInv nabla2Alpha (basis i) *
              alphaX (fun _ : Fin 1 => basis j)) +
          ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
            gInv i k * gInv j l *
                nablaAlphaX (vec2 (basis i) (basis j)) *
                nablaAlphaX (vec2 (basis k) (basis l))) := by
          simp_rw [mul_add, Finset.sum_add_distrib]
          simp_rw [Finset.mul_sum]




def OneFormNormProductRuleInBasis
    {Idx : Type*} [Fintype Idx]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (α : (y : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 y)
    (nablaAlpha : (y : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 y)
    (nabla2Alpha : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      3 x) : Prop :=
  (1 / 2 : Real) *
      laplacian (I := I) cov g
        (fun y : M => inner0S (I := I) g y 1 (α y) (α y)) x =
    oneFormRoughInnerCoord (I := I) basis gInv (α x) nabla2Alpha +
      oneFormNablaNormCoord (I := I) basis gInv (nablaAlpha x)



theorem rough_inner_eq_coord_of_trace
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M)
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis_gen (I := I) g x basis gInv)
    (αx roughAlphaX :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (nabla2Alpha : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      3 x)
    (hrough : RoughLap0SRealizesMetricTraceInBasis (I := I) basis gInv
      (s := 1) roughAlphaX nabla2Alpha) :
    inner0S (I := I) g x 1 roughAlphaX αx =
      oneFormRoughInnerCoord (I := I) basis gInv αx nabla2Alpha := by
  rw [inner0S_one_eq_cotangent, cotangentInner_eq_gen,
    cotangentInner_eq_coord_gen (I := I) g x basis gInv hinv]
  unfold oneFormRoughInnerCoord
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hrough_i :
      (cotangentToDual_gen (I := I) roughAlphaX) (basis i) =
        roughLap1FormAt (I := I) basis gInv nabla2Alpha (basis i) := by
    simpa [cotangentToDual_apply_gen] using
      roughLap1FormAt_eq_of_realizes (I := I) basis gInv roughAlphaX
        nabla2Alpha hrough (basis i)
  rw [hrough_i]
  simp [cotangentToDual_apply_gen, mul_assoc]



theorem nabla_norm_eq_coord
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M)
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis_gen (I := I) g x basis gInv)
    (nablaAlphaX :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :
    normSq0S (I := I) g x 2 nablaAlphaX =
      oneFormNablaNormCoord (I := I) basis gInv nablaAlphaX := by
  simpa [oneFormNablaNormCoord, vec2] using
    Tensor0SBundle.normSq0S_two_eq_coord (I := I) (M := M) g x
      basis gInv hinv nablaAlphaX



theorem oneForm_norm_product_rule_of_trace
    {Idx : Type*} [Fintype Idx]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (alphaRaw : (y : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 y)
    (nablaAlpha : (y : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 y)
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (normSecond :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (hlap : ScalarLaplacianRealizesTraceAtInBasis (I := I) cov g basis gInv
      (fun y : M => inner0S (I := I) g y 1 (alphaRaw y) (alphaRaw y)) normSecond)
    (htrace : MetricTraceInnerProductRuleAt (I := I) basis gInv
      (alphaRaw x) (nablaAlpha x) nabla2Alpha normSecond) :
    OneFormNormProductRuleInBasis (I := I) cov g basis gInv
      alphaRaw nablaAlpha nabla2Alpha := by
  unfold OneFormNormProductRuleInBasis ScalarLaplacianRealizesTraceAtInBasis at *
  rw [hlap, htrace]
  ring






theorem oneForm_norm_product_rule_of_metric_compatible
    {Idx : Type*} [Fintype Idx]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (_alpha : OneFormSection (I := I) (M := M))
    (alphaRaw : (y : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 y)
    (nablaAlpha : (y : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 y)
    (_nablaAlphaSec : TwoTensorSection (I := I) (M := M))
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (normSecond :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (hlap : ScalarLaplacianRealizesTraceAtInBasis (I := I) cov g basis gInv
      (fun y : M => inner0S (I := I) g y 1 (alphaRaw y) (alphaRaw y)) normSecond)
    (htrace : MetricTraceInnerProductRuleAt (I := I) basis gInv
      (alphaRaw x) (nablaAlpha x) nabla2Alpha normSecond) :
    OneFormNormProductRuleInBasis (I := I) cov g basis gInv
      alphaRaw nablaAlpha nabla2Alpha :=
  oneForm_norm_product_rule_of_trace (I := I) cov g basis gInv
    alphaRaw nablaAlpha nabla2Alpha normSecond hlap htrace



theorem oneForm_norm_second_product_of_metric_compatible
    {Idx : Type*} [Fintype Idx]
    (_cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (_g : SmoothRiemannianMetric I M)
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (_alpha : OneFormSection (I := I) (M := M))
    (alphaRaw : (y : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 y)
    (nablaAlpha : (y : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 y)
    (_nablaAlphaSec : TwoTensorSection (I := I) (M := M))
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (normSecond :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (hprod : OneFormNormSecondProductInBasis (I := I) basis gInv
      (alphaRaw x) (nablaAlpha x) nabla2Alpha normSecond) :
    MetricTraceInnerProductRuleAt (I := I) basis gInv
      (alphaRaw x) (nablaAlpha x) nabla2Alpha normSecond :=
  metricTrace_inner_product_rule_of_second_product (I := I) basis gInv
    (alphaRaw x) (nablaAlpha x) nabla2Alpha normSecond hprod





theorem oneForm_norm_bochner_coord
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis_gen (I := I) g x basis gInv)
    (α roughAlpha : (y : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 y)
    (nablaAlpha : (y : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 y)
    (nabla2Alpha : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      3 x)
    (hprod : OneFormNormProductRuleInBasis (I := I) cov g basis gInv
      α nablaAlpha nabla2Alpha)
    (_hrough : RoughLap0SRealizesMetricTraceInBasis (I := I) basis gInv
      (s := 1) (roughAlpha x) nabla2Alpha) :
    OneFormNormBochnerAt (I := I) cov g α roughAlpha nablaAlpha x := by
  unfold OneFormNormBochnerAt
  rw [hprod]
  rw [rough_inner_eq_coord_of_trace (I := I) g basis gInv hinv
    (α x) (roughAlpha x) nabla2Alpha _hrough]
  rw [nabla_norm_eq_coord (I := I) g basis gInv hinv (nablaAlpha x)]


theorem oneForm_norm_bochner_at
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis_gen (I := I) g x basis gInv)
    (α roughAlpha : (y : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 y)
    (nablaAlpha : (y : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 y)
    (nabla2Alpha : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      3 x)
    (hprod : OneFormNormProductRuleInBasis (I := I) cov g basis gInv
      α nablaAlpha nabla2Alpha)
    (hrough : RoughLap0SRealizesMetricTraceInBasis (I := I) basis gInv
      (s := 1) (roughAlpha x) nabla2Alpha) :
    OneFormNormBochnerAt (I := I) cov g α roughAlpha nablaAlpha x :=
  oneForm_norm_bochner_coord (I := I) cov g basis gInv hinv
    α roughAlpha nablaAlpha nabla2Alpha hprod hrough



theorem hessian_realizes_nabla_du
    (g : SmoothRiemannianMetric I M)
    (Hess nablaDu : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (x : M) (h : nablaDu x = Hess x) :
    HessianNormRealizesNablaDifferentialAt (I := I) g Hess nablaDu x := by
  unfold HessianNormRealizesNablaDifferentialAt hessianNormSq
  rw [h]



theorem hessian_norm_realizes_of_nabla_du
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M)
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (Hess nablaDu : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (hcomp : ∀ slots : Fin 2 -> Idx,
      component0S (I := I) basis (nablaDu x) slots =
        component0S (I := I) basis (Hess x) slots) :
    HessianNormRealizesNablaDifferentialAt (I := I) g Hess nablaDu x :=
  hessian_realizes_nabla_du (I := I) g Hess nablaDu x
    (ext0S_basis (I := I) basis hcomp)



theorem hessian_components_of_nabla_du
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (X : Idx -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (du : OneFormSection (I := I) (M := M))
    (Hess nablaDu : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (hfields : SmoothBasisFieldsAt (I := I) basis X)
    (hHess : HessianRealizesNablaDuAt (I := I) cov du Hess x)
    (hnabla : NablaOneFormRealizesAt (I := I) cov du nablaDu x) :
    ∀ slots : Fin 2 -> Idx,
      component0S (I := I) basis (nablaDu x) slots =
        component0S (I := I) basis (Hess x) slots := by
  intro slots
  let X0 := X (slots 0)
  let Y := basis (slots 1)
  have hvec : vec2 (X0 x) Y = fun a : Fin 2 => basis (slots a) := by
    funext a
    fin_cases a
    · simp [X0, Y, vec2, DifferentialGeometry.Integral.Connection.vec2, hfields (slots 0)]
    · simp [Y, vec2, DifferentialGeometry.Integral.Connection.vec2]
  have hn := hnabla X0 Y
  have hh := hHess X0 Y
  change nablaDu x (fun a : Fin 2 => basis (slots a)) =
    Hess x (fun a : Fin 2 => basis (slots a))
  rw [← hvec]
  rw [hn, hh]
  rfl


theorem roughLap_du_eq_d_lap_add_ric_of_comm
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    (Ric : Tensor02Section (I := I) (M := M))
    (u : M -> Real)
    (roughDu : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (x : M)
    (hcomm : DifferentialOneFormCommutatorAt (I := I) cov g Ric u roughDu x) :
    inner0S (I := I) g x 1 (roughDu x) (differential1FormFun (I := I) u x) =
      inner0S (I := I) g x 1
          (differential1FormFun (I := I) (laplacian (I := I) cov g u) x)
          (differential1FormFun (I := I) u x) +
        ricciGradGrad (I := I) Ric g u x :=
  hcomm






theorem oneForm_ricci_identity_components
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    (Ric : Tensor02Section (I := I) (M := M))
    (Rm13 : Tensor13Section (I := I) (M := M))
    (u : M -> Real)
    (roughDu : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (duSec : OneFormSection (I := I) (M := M))
    (nablaDu : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (nablaDuSec : TwoTensorSection (I := I) (M := M))
    (nabla2Du :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (_hinv : MetricInverseInBasis_gen (I := I) g x basis gInv)
    (_hRm : Rm13RealizesConnection (I := I) cov Rm13)
    (_hRic : RicciTensorRealizesRm13Trace (I := I) Ric Rm13)
    (_hdu : DuFieldRealizes (I := I) u duSec)
    (_hnabla : NablaOneFormRealizesAt (I := I) cov duSec nablaDu x)
    (_hnabla2 : Nabla2OneFormRealizesAt (I := I) cov duSec nablaDuSec x nabla2Du)
    (hrough : RoughLap0SRealizesMetricTrace (I := I) g (s := 1) (roughDu x) nabla2Du)
    (hdlap : TraceNablaHessianRealizesDLapAt (I := I) cov g u nabla2Du)
    (hcomm : OneFormRicciTraceCommAt (I := I) g Ric u basis gInv nabla2Du) :
    OneFormCommutatorEvalAt (I := I) cov g Ric u roughDu x := by
  have hroughBasis : RoughLap0SRealizesMetricTraceInBasis (I := I) basis gInv
      (s := 1) (roughDu x) nabla2Du :=
    rough_lap_one_form_realizes_metric_trace (I := I) g basis gInv
      nabla2Du (roughDu x) hrough _hinv
  have hdlapBasis : TraceNablaHessianRealizesDLapAtInBasis (I := I)
      cov g basis gInv u nabla2Du :=
    TraceNablaHessianRealizesDLapAt.toInBasis (I := I) cov g basis gInv
      _hinv u nabla2Du hdlap
  intro Y
  calc
    roughDu x (fun _ : Fin 1 => Y)
        = roughLap1FormAt (I := I) basis gInv nabla2Du Y := by
          exact roughLap1FormAt_eq_of_realizes (I := I) basis gInv (roughDu x)
            nabla2Du hroughBasis Y
    _ = traceNablaHessianForDLapInBasis (I := I) basis gInv nabla2Du Y +
          Ric x (vec2 Y (gradientFun (I := I) g u x)) := by
          simpa [OneFormRicciTraceCommAt, traceNablaHessianForDLapInBasis] using
            (show OneFormRicciTraceCommWithVectorAt (I := I) Ric basis gInv
              (gradientFun (I := I) g u x) nabla2Du from hcomm) Y
    _ = differential1FormFun (I := I) (laplacian (I := I) cov g u) x
            (fun _ : Fin 1 => Y) +
          Ric x (vec2 Y (gradientFun (I := I) g u x)) := by
          rw [hdlapBasis Y]







theorem one_form_ricci_trace_comm_of_lc
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    (Ric : Tensor02Section (I := I) (M := M))
    (Rm13 : Tensor13Section (I := I) (M := M))
    (u : M -> Real)
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (duSec : OneFormSection (I := I) (M := M))
    (nablaDu : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (nablaDuSec : TwoTensorSection (I := I) (M := M))
    (nabla2Du :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (_hinv : MetricInverseInBasis_gen (I := I) g x basis gInv)
    (_hRm : Rm13RealizesConnection (I := I) cov Rm13)
    (_hRic : RicciTensorRealizesRm13Trace (I := I) Ric Rm13)
    (_hdu : DuFieldRealizes (I := I) u duSec)
    (_hnabla : NablaOneFormRealizesAt (I := I) cov duSec nablaDu x)
    (_hnabla2 : Nabla2OneFormRealizesAt (I := I) cov duSec nablaDuSec x nabla2Du)
    (hsymm : OneFormLastTwoSymmAt (I := I) nabla2Du)
    (hthird : OneFormThirdCovDerivCommAt (I := I) Rm13
      (differential1FormFun (I := I) u x) nabla2Du)
    (hSkew : Rm13MetricSkewAt (I := I) g x (Rm13 x)) :
    OneFormRicciTraceCommAt (I := I) g Ric u basis gInv nabla2Du := by
  exact oneForm_ricci_trace_comm_of_third_comm (I := I) Ric Rm13
    (differential1FormFun (I := I) u x) basis gInv
    (gradientFun (I := I) g u x) nabla2Du hsymm hthird
    (by
      have hcurv := curvatureTraceDuEqRicciGradAt_of_metric_dual
        (I := I) g Ric Rm13 u basis gInv _hinv _hRic hSkew
      intro Y
      simpa [CurvatureTraceDuEqRicciGradAt, curvatureTraceDuAt,
        curvatureTraceOneFormAt] using hcurv Y)



theorem oneForm_commutator_eval_of_components
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    (Ric : Tensor02Section (I := I) (M := M))
    (Rm13 : Tensor13Section (I := I) (M := M))
    (u : M -> Real)
    (roughDu : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (duSec : OneFormSection (I := I) (M := M))
    (nablaDu : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (nablaDuSec : TwoTensorSection (I := I) (M := M))
    (nabla2Du :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (hinv : MetricInverseInBasis_gen (I := I) g x basis gInv)
    (hRm : Rm13RealizesConnection (I := I) cov Rm13)
    (hRic : RicciTensorRealizesRm13Trace (I := I) Ric Rm13)
    (hdu : DuFieldRealizes (I := I) u duSec)
    (hnabla : NablaOneFormRealizesAt (I := I) cov duSec nablaDu x)
    (hnabla2 : Nabla2OneFormRealizesAt (I := I) cov duSec nablaDuSec x nabla2Du)
    (hrough : RoughLap0SRealizesMetricTrace (I := I) g (s := 1) (roughDu x) nabla2Du)
    (hdlap : TraceNablaHessianRealizesDLapAt (I := I) cov g u nabla2Du)
    (hcomm : OneFormRicciTraceCommAt (I := I) g Ric u basis gInv nabla2Du) :
    OneFormCommutatorEvalAt (I := I) cov g Ric u roughDu x :=
  oneForm_ricci_identity_components (I := I) cov g Ric Rm13 u roughDu
    basis gInv duSec nablaDu nablaDuSec nabla2Du
    hinv hRm hRic hdu hnabla hnabla2 hrough hdlap hcomm



theorem oneForm_commutator_eval_of_lc
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    (Ric : Tensor02Section (I := I) (M := M))
    (Rm13 : Tensor13Section (I := I) (M := M))
    (u : M -> Real)
    (roughDu : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (duSec : OneFormSection (I := I) (M := M))
    (nablaDu : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (nablaDuSec : TwoTensorSection (I := I) (M := M))
    (nabla2Du :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (hinv : MetricInverseInBasis_gen (I := I) g x basis gInv)
    (hRm : Rm13RealizesConnection (I := I) cov Rm13)
    (hRic : RicciTensorRealizesRm13Trace (I := I) Ric Rm13)
    (hdu : DuFieldRealizes (I := I) u duSec)
    (hnabla : NablaOneFormRealizesAt (I := I) cov duSec nablaDu x)
    (hnabla2 : Nabla2OneFormRealizesAt (I := I) cov duSec nablaDuSec x nabla2Du)
    (hsymm : OneFormLastTwoSymmAt (I := I) nabla2Du)
    (hthird : OneFormThirdCovDerivCommAt (I := I) Rm13
      (differential1FormFun (I := I) u x) nabla2Du)
    (hSkew : Rm13MetricSkewAt (I := I) g x (Rm13 x))
    (hrough : RoughLap0SRealizesMetricTrace (I := I) g (s := 1) (roughDu x) nabla2Du)
    (hdlap : TraceNablaHessianRealizesDLapAt (I := I) cov g u nabla2Du) :
    OneFormCommutatorEvalAt (I := I) cov g Ric u roughDu x :=
  oneForm_commutator_eval_of_components (I := I) cov g Ric Rm13 u roughDu
    basis gInv duSec nablaDu nablaDuSec nabla2Du
    hinv hRm hRic hdu hnabla hnabla2 hrough hdlap
    (one_form_ricci_trace_comm_of_lc (I := I) cov g Ric Rm13 u basis gInv
      duSec nablaDu nablaDuSec nabla2Du
      hinv hRm hRic hdu hnabla hnabla2 hsymm hthird hSkew)



theorem roughLap_du_eq_d_lap_add_ric
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    (Ric : Tensor02Section (I := I) (M := M))
    (u : M -> Real)
    (roughDu : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (x : M)
    (hcomm : OneFormCommutatorEvalAt (I := I) cov g Ric u roughDu x) :
    inner0S (I := I) g x 1 (roughDu x) (differential1FormFun (I := I) u x) =
      inner0S (I := I) g x 1
          (differential1FormFun (I := I) (laplacian (I := I) cov g u) x)
          (differential1FormFun (I := I) u x) +
        ricciGradGrad (I := I) Ric g u x :=
  oneForm_commutator_pair_of_eval (I := I) cov g Ric u roughDu x hcomm



theorem half_laplacian_gradNormSq_eq
    {Idx : Type*} [Fintype Idx]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    (Ric : Tensor02Section (I := I) (M := M))
    (Rm04 : Tensor04Section (I := I) (M := M))
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (_hRic : RicciTensorRealizesRm04TraceInFrame (I := I) Ric Rm04 gInv frame)
    (u : M -> Real)
    (Hess nablaDu : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (roughDu : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (x : M)
    (h_norm : OneFormNormBochnerAt (I := I) cov g
      (differential1FormFun (I := I) u) roughDu nablaDu x)
    (h_comm : DifferentialOneFormCommutatorAt (I := I) cov g Ric u roughDu x)
    (h_hess : HessianNormRealizesNablaDifferentialAt (I := I) g Hess nablaDu x) :
    (1 / 2 : Real) * laplacian (I := I) cov g (gradNormSq (I := I) g u) x =
      g.inner x
          (gradientFun (I := I) g (laplacian (I := I) cov g u) x)
          (gradientFun (I := I) g u x) +
        hessianNormSq (I := I) g Hess x +
          ricciGradGrad (I := I) Ric g u x := by
  have h_norm_fun :
      (fun y : M =>
          inner0S (I := I) g y 1
            (differential1FormFun (I := I) u y)
            (differential1FormFun (I := I) u y)) =
        gradNormSq (I := I) g u := by
    funext y
    exact inner0S_differential1FormFun_eq_gradNormSq (I := I) g u y
  rw [← h_norm_fun]
  rw [h_norm, h_comm, h_hess]
  rw [inner0S_differential1FormFun_pair_eq_grad_inner]
  ring






theorem fundamental_bochner
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    (Ric : Tensor02Section (I := I) (M := M))
    (Rm04 : Tensor04Section (I := I) (M := M))
    (gInvFrame : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hRic04 : RicciTensorRealizesRm04TraceInFrame (I := I) Ric Rm04 gInvFrame frame)
    (u : M -> Real)
    (Hess nablaDu : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (roughDu : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInvAt : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis_gen (I := I) g x basis gInvAt)
    (nabla2Du :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (normSecond :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (hlap :
      laplacian (I := I) cov g
        (fun y : M =>
          inner0S (I := I) g y 1
            (differential1FormFun (I := I) u y)
            (differential1FormFun (I := I) u y)) x =
        scalarLapTraceAt (I := I) g normSecond)
    (htrace : MetricTraceInnerProductRuleAt (I := I) basis gInvAt
      (differential1FormFun (I := I) u x) (nablaDu x) nabla2Du normSecond)
    (hrough : RoughLap0SRealizesMetricTrace (I := I) g (s := 1) (roughDu x) nabla2Du)
    (hcomm : OneFormCommutatorEvalAt (I := I) cov g Ric u roughDu x)
    (hHessComp : ∀ slots : Fin 2 -> Idx,
      component0S (I := I) basis (nablaDu x) slots =
        component0S (I := I) basis (Hess x) slots) :
    (1 / 2 : Real) * laplacian (I := I) cov g (gradNormSq (I := I) g u) x =
      g.inner x
          (gradientFun (I := I) g (laplacian (I := I) cov g u) x)
          (gradientFun (I := I) g u x) +
        hessianNormSq (I := I) g Hess x +
          ricciGradGrad (I := I) Ric g u x := by
  have hlapBasis : ScalarLaplacianRealizesTraceAtInBasis (I := I) cov g basis gInvAt
      (fun y : M =>
        inner0S (I := I) g y 1
          (differential1FormFun (I := I) u y)
          (differential1FormFun (I := I) u y)) normSecond :=
    ScalarLaplacianRealizesTraceAt.toInBasis (I := I) cov g basis gInvAt
      hinv
      (fun y : M =>
          inner0S (I := I) g y 1
            (differential1FormFun (I := I) u y)
            (differential1FormFun (I := I) u y)) normSecond
          (scalar_laplacian_trace_of_pair (I := I) cov g
            (fun y : M =>
              inner0S (I := I) g y 1
                (differential1FormFun (I := I) u y)
                (differential1FormFun (I := I) u y)) normSecond hlap)
  have hroughBasis : RoughLap0SRealizesMetricTraceInBasis (I := I) basis gInvAt
      (s := 1) (roughDu x) nabla2Du :=
    rough_lap_one_form_realizes_metric_trace (I := I) g basis gInvAt
      nabla2Du (roughDu x) hrough hinv
  refine half_laplacian_gradNormSq_eq (I := I) cov g Ric Rm04 gInvFrame frame
    hRic04 u Hess nablaDu roughDu x ?_ ?_ ?_
  · exact oneForm_norm_bochner_at (I := I) cov g basis gInvAt hinv
      (differential1FormFun (I := I) u) roughDu nablaDu nabla2Du
      (oneForm_norm_product_rule_of_trace (I := I) cov g basis gInvAt
        (differential1FormFun (I := I) u) nablaDu nabla2Du normSecond hlapBasis htrace)
      hroughBasis
  · exact oneForm_commutator_pair_of_eval (I := I) cov g Ric u roughDu x hcomm
  · exact hessian_norm_realizes_of_nabla_du (I := I) g basis Hess nablaDu hHessComp




theorem fundamental_bochner_of_terms
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    (Ric : Tensor02Section (I := I) (M := M))
    (Rm04 : Tensor04Section (I := I) (M := M))
    (gInvFrame : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hRic04 : RicciTensorRealizesRm04TraceInFrame (I := I) Ric Rm04 gInvFrame frame)
    (u : M -> Real)
    (Hess nablaDu : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (roughDu : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInvAt : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis_gen (I := I) g x basis gInvAt)
    (X : Idx -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (duSec : OneFormSection (I := I) (M := M))
    (nablaDuSec : TwoTensorSection (I := I) (M := M))
    (nabla2Du :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (normSecond :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (hfields : SmoothBasisFieldsAt (I := I) basis X)
    (hHess : HessianRealizesNablaDuAt (I := I) cov duSec Hess x)
    (hnabla : NablaOneFormRealizesAt (I := I) cov duSec nablaDu x)
    (_hnabla2 : Nabla2OneFormRealizesAt (I := I) cov duSec nablaDuSec x nabla2Du)
    (hlapTrace :
      laplacian (I := I) cov g
        (fun y : M =>
          inner0S (I := I) g y 1
            (differential1FormFun (I := I) u y)
            (differential1FormFun (I := I) u y)) x =
        metricTrace0S2InBasis (I := I) basis gInvAt normSecond Fin.elim0)
    (hsecond : OneFormNormSecondProductInBasis (I := I) basis gInvAt
      (differential1FormFun (I := I) u x) (nablaDu x) nabla2Du normSecond)
    (hrough : RoughLap0SRealizesMetricTrace (I := I) g (s := 1) (roughDu x) nabla2Du)
    (hcomm : OneFormCommutatorEvalAt (I := I) cov g Ric u roughDu x) :
    (1 / 2 : Real) * laplacian (I := I) cov g (gradNormSq (I := I) g u) x =
      g.inner x
          (gradientFun (I := I) g (laplacian (I := I) cov g u) x)
          (gradientFun (I := I) g u x) +
        hessianNormSq (I := I) g Hess x +
          ricciGradGrad (I := I) Ric g u x := by
  refine fundamental_bochner (I := I) cov g Ric Rm04 gInvFrame frame
    hRic04 u Hess nablaDu roughDu basis gInvAt hinv nabla2Du normSecond
    ?_ ?_ hrough hcomm ?_
  · rw [hlapTrace]
    rw [metricTrace0S2InBasis_eq_metricTrace (I := I) g basis gInvAt
      hinv normSecond Fin.elim0]
    rw [← scalarLapTraceAt_eq_firstTwo (I := I) g normSecond]
  · exact oneForm_norm_second_product_of_metric_compatible (I := I) cov g
      basis gInvAt duSec (differential1FormFun (I := I) u) nablaDu
      nablaDuSec nabla2Du normSecond hsecond
  · exact hessian_components_of_nabla_du (I := I) cov basis X duSec Hess
      nablaDu hfields hHess hnabla







theorem fundamental_bochner_of_terms_of_normSecond_realizes
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    (hmc : DifferentialGeometry.Integral.Connection.IsMetricCompatible_gen (I := I) cov g)
    (Ric : Tensor02Section (I := I) (M := M))
    (Rm04 : Tensor04Section (I := I) (M := M))
    (gInvFrame : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hRic04 : RicciTensorRealizesRm04TraceInFrame (I := I) Ric Rm04 gInvFrame frame)
    (u : M -> Real)
    (Hess nablaDu : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (roughDu : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInvAt : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis_gen (I := I) g x basis gInvAt)
    (X : Idx -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (duSec normDuSec : OneFormSection (I := I) (M := M))
    (nablaDuSec : TwoTensorSection (I := I) (M := M))
    (nabla2Du :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (normSecond :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (normSecondSec : (y : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 y)
    (hfields : SmoothBasisFieldsAt (I := I) basis X)
    (hHess : HessianRealizesNablaDuAt (I := I) cov duSec Hess x)
    (hnabla : NablaOneFormRealizesAt (I := I) cov duSec nablaDu x)
    (_hnabla2 : Nabla2OneFormRealizesAt (I := I) cov duSec nablaDuSec x nabla2Du)
    (hnormSecond : normSecondSec x = normSecond)
    (hnormDu : DuFieldRealizes (I := I)
      (fun y : M =>
        inner0S (I := I) g y 1
          (differential1FormFun (I := I) u y)
          (differential1FormFun (I := I) u y)) normDuSec)
    (hnormHess : HessianRealizesNablaDuAt (I := I) cov normDuSec normSecondSec x)
    (hnormGrad : MDiffAt (T% fun y : M =>
      gradientFun (I := I) g
        (fun z : M =>
          inner0S (I := I) g z 1
            (differential1FormFun (I := I) u z)
            (differential1FormFun (I := I) u z)) y) x)
    (hsecond : OneFormNormSecondProductInBasis (I := I) basis gInvAt
      (differential1FormFun (I := I) u x) (nablaDu x) nabla2Du normSecond)
    (hrough : RoughLap0SRealizesMetricTrace (I := I) g (s := 1) (roughDu x) nabla2Du)
    (hcomm : OneFormCommutatorEvalAt (I := I) cov g Ric u roughDu x) :
    (1 / 2 : Real) * laplacian (I := I) cov g (gradNormSq (I := I) g u) x =
      g.inner x
          (gradientFun (I := I) g (laplacian (I := I) cov g u) x)
          (gradientFun (I := I) g u x) +
        hessianNormSq (I := I) g Hess x +
          ricciGradGrad (I := I) Ric g u x := by
  have hlapDirect :
      laplacian (I := I) cov g
      (fun y : M =>
        inner0S (I := I) g y 1
          (differential1FormFun (I := I) u y)
          (differential1FormFun (I := I) u y)) x =
        scalarLapTraceAt (I := I) g normSecond := by
    simpa [hnormSecond] using
      scalarLapTraceAt_of_nablaDu (I := I) cov g hmc basis gInvAt
        hinv
        (fun y : M =>
          inner0S (I := I) g y 1
            (differential1FormFun (I := I) u y)
            (differential1FormFun (I := I) u y))
        normDuSec normSecondSec X hfields hnormDu hnormHess hnormGrad
  refine fundamental_bochner (I := I) cov g Ric Rm04 gInvFrame frame
    hRic04 u Hess nablaDu roughDu basis gInvAt hinv nabla2Du normSecond
    hlapDirect ?_ hrough hcomm ?_
  · exact oneForm_norm_second_product_of_metric_compatible (I := I) cov g
      basis gInvAt duSec (differential1FormFun (I := I) u) nablaDu
      nablaDuSec nabla2Du normSecond hsecond
  · exact hessian_components_of_nabla_du (I := I) cov basis X duSec Hess
      nablaDu hfields hHess hnabla



theorem fundamental_bochner_of_components
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    (Ric : Tensor02Section (I := I) (M := M))
    (Rm13 : Tensor13Section (I := I) (M := M))
    (Rm04 : Tensor04Section (I := I) (M := M))
    (gInvFrame : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hRm13 : Rm13RealizesConnection (I := I) cov Rm13)
    (hRic13 : RicciTensorRealizesRm13Trace (I := I) Ric Rm13)
    (hRic04 : RicciTensorRealizesRm04TraceInFrame (I := I) Ric Rm04 gInvFrame frame)
    (u : M -> Real)
    (Hess nablaDu : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (roughDu : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInvAt : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis_gen (I := I) g x basis gInvAt)
    (duSec : OneFormSection (I := I) (M := M))
    (nablaDuSec : TwoTensorSection (I := I) (M := M))
    (nabla2Du :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (normSecond :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (hdu : DuFieldRealizes (I := I) u duSec)
    (hnabla : NablaOneFormRealizesAt (I := I) cov duSec nablaDu x)
    (hnabla2 : Nabla2OneFormRealizesAt (I := I) cov duSec nablaDuSec x nabla2Du)
    (hlap :
      laplacian (I := I) cov g
        (fun y : M =>
          inner0S (I := I) g y 1
            (differential1FormFun (I := I) u y)
            (differential1FormFun (I := I) u y)) x =
        scalarLapTraceAt (I := I) g normSecond)
    (htrace : MetricTraceInnerProductRuleAt (I := I) basis gInvAt
      (differential1FormFun (I := I) u x) (nablaDu x) nabla2Du normSecond)
    (hrough : RoughLap0SRealizesMetricTrace (I := I) g (s := 1) (roughDu x) nabla2Du)
    (hdlap : TraceNablaHessianRealizesDLapAt (I := I) cov g u nabla2Du)
    (hricciComm : OneFormRicciTraceCommAt (I := I) g Ric u basis gInvAt nabla2Du)
    (hHessComp : ∀ slots : Fin 2 -> Idx,
      component0S (I := I) basis (nablaDu x) slots =
        component0S (I := I) basis (Hess x) slots) :
    (1 / 2 : Real) * laplacian (I := I) cov g (gradNormSq (I := I) g u) x =
      g.inner x
          (gradientFun (I := I) g (laplacian (I := I) cov g u) x)
          (gradientFun (I := I) g u x) +
        hessianNormSq (I := I) g Hess x +
          ricciGradGrad (I := I) Ric g u x := by
  refine fundamental_bochner (I := I) cov g Ric Rm04 gInvFrame frame
    hRic04 u Hess nablaDu roughDu basis gInvAt hinv nabla2Du normSecond
    hlap htrace hrough ?_ hHessComp
  exact oneForm_commutator_eval_of_components (I := I) cov g Ric Rm13 u roughDu
    basis gInvAt duSec nablaDu nablaDuSec nabla2Du
    hinv hRm13 hRic13 hdu hnabla hnabla2 hrough hdlap hricciComm







theorem fundamental_bochner_of_lc
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    [SigmaCompactSpace M] [T2Space M]
    (g : SmoothRiemannianMetric I M)
    (Ric : Tensor02Section (I := I) (M := M))
    (Rm13 : Tensor13Section (I := I) (M := M))
    (Rm04 : Tensor04Section (I := I) (M := M))
    (gInvFrame : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hRm13 : Rm13RealizesConnection (I := I)
      (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) g) Rm13)
    (hRic13 : RicciTensorRealizesRm13Trace (I := I) Ric Rm13)
    (hRic04 : RicciTensorRealizesRm04TraceInFrame (I := I) Ric Rm04 gInvFrame frame)
    (u : M -> Real)
    (Hess nablaDu : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (roughDu : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInvAt : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis_gen (I := I) g x basis gInvAt)
    (duSec : OneFormSection (I := I) (M := M))
    (nablaDuSec : TwoTensorSection (I := I) (M := M))
    (nabla2Du :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (normSecond :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (hdu : DuFieldRealizes (I := I) u duSec)
    (hnabla : NablaOneFormRealizesAt (I := I)
      (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) g) duSec nablaDu x)
    (hnabla2 : Nabla2OneFormRealizesAt (I := I)
      (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) g) duSec nablaDuSec x nabla2Du)
    (hlap :
      laplacian (I := I)
        (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) g) g
        (fun y : M =>
          inner0S (I := I) g y 1
            (differential1FormFun (I := I) u y)
            (differential1FormFun (I := I) u y)) x =
        scalarLapTraceAt (I := I) g normSecond)
    (htrace : MetricTraceInnerProductRuleAt (I := I) basis gInvAt
      (differential1FormFun (I := I) u x) (nablaDu x) nabla2Du normSecond)
    (hrough : RoughLap0SRealizesMetricTrace (I := I) g (s := 1) (roughDu x) nabla2Du)
    (hdlap : TraceNablaHessianRealizesDLapAt (I := I)
      (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) g) g u nabla2Du)
    (hsymm : OneFormLastTwoSymmAt (I := I) nabla2Du)
    (hthird : OneFormThirdCovDerivCommAt (I := I) Rm13
      (differential1FormFun (I := I) u x) nabla2Du)
    (hSkew : Rm13MetricSkewAt (I := I) g x (Rm13 x))
    (hHessComp : ∀ slots : Fin 2 -> Idx,
      component0S (I := I) basis (nablaDu x) slots =
        component0S (I := I) basis (Hess x) slots) :
    (1 / 2 : Real) * laplacian (I := I)
        (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) g) g
        (gradNormSq (I := I) g u) x =
      g.inner x
          (gradientFun (I := I) g
            (laplacian (I := I)
              (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) g) g u) x)
          (gradientFun (I := I) g u x) +
        hessianNormSq (I := I) g Hess x +
          ricciGradGrad (I := I) Ric g u x := by
  refine fundamental_bochner_of_components (I := I)
    (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) g) g Ric Rm13 Rm04
    gInvFrame frame hRm13 hRic13 hRic04 u Hess nablaDu roughDu
    basis gInvAt hinv duSec nablaDuSec nabla2Du normSecond
    hdu hnabla hnabla2 hlap htrace hrough hdlap ?_ hHessComp
  exact one_form_ricci_trace_comm_of_lc (I := I)
    (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) g) g Ric Rm13 u basis
    gInvAt duSec nablaDu nablaDuSec nabla2Du
    hinv hRm13 hRic13 hdu hnabla hnabla2 hsymm hthird hSkew




theorem fundamental_bochner_of_lc_terms
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    [SigmaCompactSpace M] [T2Space M]
    (g : SmoothRiemannianMetric I M)
    (Ric : Tensor02Section (I := I) (M := M))
    (Rm13 : Tensor13Section (I := I) (M := M))
    (Rm04 : Tensor04Section (I := I) (M := M))
    (gInvFrame : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hRm13 : Rm13RealizesConnection (I := I)
      (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) g) Rm13)
    (hRic13 : RicciTensorRealizesRm13Trace (I := I) Ric Rm13)
    (hRic04 : RicciTensorRealizesRm04TraceInFrame (I := I) Ric Rm04 gInvFrame frame)
    (u : M -> Real)
    (Hess nablaDu : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (roughDu : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInvAt : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis_gen (I := I) g x basis gInvAt)
    (X : Idx -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (duSec : OneFormSection (I := I) (M := M))
    (nablaDuSec : TwoTensorSection (I := I) (M := M))
    (nabla2Du :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (normSecond :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (hfields : SmoothBasisFieldsAt (I := I) basis X)
    (hHess : HessianRealizesNablaDuAt (I := I)
      (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) g) duSec Hess x)
    (hdu : DuFieldRealizes (I := I) u duSec)
    (hnabla : NablaOneFormRealizesAt (I := I)
      (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) g) duSec nablaDu x)
    (hnabla2 : Nabla2OneFormRealizesAt (I := I)
      (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) g) duSec nablaDuSec x nabla2Du)
    (hlapTrace :
      laplacian (I := I)
        (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) g) g
        (fun y : M =>
          inner0S (I := I) g y 1
            (differential1FormFun (I := I) u y)
            (differential1FormFun (I := I) u y)) x =
        metricTrace0S2InBasis (I := I) basis gInvAt normSecond Fin.elim0)
    (hsecond : OneFormNormSecondProductInBasis (I := I) basis gInvAt
      (differential1FormFun (I := I) u x) (nablaDu x) nabla2Du normSecond)
    (hrough : RoughLap0SRealizesMetricTrace (I := I) g (s := 1) (roughDu x) nabla2Du)
    (hdlap : TraceNablaHessianRealizesDLapAt (I := I)
      (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) g) g u nabla2Du)
    (hsymm : OneFormLastTwoSymmAt (I := I) nabla2Du)
    (hthird : OneFormThirdCovDerivCommAt (I := I) Rm13
      (differential1FormFun (I := I) u x) nabla2Du)
    (hSkew : Rm13MetricSkewAt (I := I) g x (Rm13 x)) :
    (1 / 2 : Real) * laplacian (I := I)
        (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) g) g
        (gradNormSq (I := I) g u) x =
      g.inner x
          (gradientFun (I := I) g
            (laplacian (I := I)
              (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) g) g u) x)
          (gradientFun (I := I) g u x) +
        hessianNormSq (I := I) g Hess x +
          ricciGradGrad (I := I) Ric g u x := by
  refine fundamental_bochner_of_lc (I := I) g Ric Rm13 Rm04
    gInvFrame frame hRm13 hRic13 hRic04 u Hess nablaDu roughDu
    basis gInvAt hinv duSec nablaDuSec nabla2Du normSecond
    hdu hnabla hnabla2 ?_ ?_ hrough hdlap hsymm hthird hSkew ?_
  · rw [hlapTrace]
    rw [metricTrace0S2InBasis_eq_metricTrace (I := I) g basis gInvAt
      hinv normSecond Fin.elim0]
    rw [← scalarLapTraceAt_eq_firstTwo (I := I) g normSecond]
  · exact oneForm_norm_second_product_of_metric_compatible (I := I)
      (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) g) g
      basis gInvAt duSec (differential1FormFun (I := I) u) nablaDu
      nablaDuSec nabla2Du normSecond hsecond
  · exact hessian_components_of_nabla_du (I := I)
      (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) g) basis X duSec Hess
      nablaDu hfields hHess hnabla




theorem fundamental_bochner_of_lc_terms_of_normSecond_realizes
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    [SigmaCompactSpace M] [T2Space M]
    (g : SmoothRiemannianMetric I M)
    (Ric : Tensor02Section (I := I) (M := M))
    (Rm13 : Tensor13Section (I := I) (M := M))
    (Rm04 : Tensor04Section (I := I) (M := M))
    (gInvFrame : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hRm13 : Rm13RealizesConnection (I := I)
      (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) g) Rm13)
    (hRic13 : RicciTensorRealizesRm13Trace (I := I) Ric Rm13)
    (hRic04 : RicciTensorRealizesRm04TraceInFrame (I := I) Ric Rm04 gInvFrame frame)
    (u : M -> Real)
    (Hess nablaDu : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (roughDu : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInvAt : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis_gen (I := I) g x basis gInvAt)
    (X : Idx -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (duSec normDuSec : OneFormSection (I := I) (M := M))
    (nablaDuSec : TwoTensorSection (I := I) (M := M))
    (nabla2Du :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (normSecond :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (normSecondSec : (y : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 y)
    (hfields : SmoothBasisFieldsAt (I := I) basis X)
    (hHess : HessianRealizesNablaDuAt (I := I)
      (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) g) duSec Hess x)
    (hdu : DuFieldRealizes (I := I) u duSec)
    (hnabla : NablaOneFormRealizesAt (I := I)
      (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) g) duSec nablaDu x)
    (hnabla2 : Nabla2OneFormRealizesAt (I := I)
      (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) g) duSec nablaDuSec x nabla2Du)
    (hnormSecond : normSecondSec x = normSecond)
    (hnormDu : DuFieldRealizes (I := I)
      (fun y : M =>
        inner0S (I := I) g y 1
          (differential1FormFun (I := I) u y)
          (differential1FormFun (I := I) u y)) normDuSec)
    (hnormHess : HessianRealizesNablaDuAt (I := I)
      (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) g)
      normDuSec normSecondSec x)
    (hnormGrad : MDiffAt (T% fun y : M =>
      gradientFun (I := I) g
        (fun z : M =>
          inner0S (I := I) g z 1
            (differential1FormFun (I := I) u z)
            (differential1FormFun (I := I) u z)) y) x)
    (hsecond : OneFormNormSecondProductInBasis (I := I) basis gInvAt
      (differential1FormFun (I := I) u x) (nablaDu x) nabla2Du normSecond)
    (hrough : RoughLap0SRealizesMetricTrace (I := I) g (s := 1) (roughDu x) nabla2Du)
    (hdlap : TraceNablaHessianRealizesDLapAt (I := I)
      (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) g) g u nabla2Du)
    (hsymm : OneFormLastTwoSymmAt (I := I) nabla2Du)
    (hthird : OneFormThirdCovDerivCommAt (I := I) Rm13
      (differential1FormFun (I := I) u x) nabla2Du)
    (hSkew : Rm13MetricSkewAt (I := I) g x (Rm13 x)) :
    (1 / 2 : Real) * laplacian (I := I)
        (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) g) g
        (gradNormSq (I := I) g u) x =
      g.inner x
          (gradientFun (I := I) g
            (laplacian (I := I)
              (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) g) g u) x)
          (gradientFun (I := I) g u x) +
        hessianNormSq (I := I) g Hess x +
          ricciGradGrad (I := I) Ric g u x := by
  have hlapDirect :
      laplacian (I := I)
      (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) g) g
      (fun y : M =>
        inner0S (I := I) g y 1
          (differential1FormFun (I := I) u y)
          (differential1FormFun (I := I) u y)) x =
        scalarLapTraceAt (I := I) g normSecond := by
    simpa [hnormSecond] using
      scalarLapTraceAt_of_nablaDu (I := I)
        (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) g) g
        (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric_isMetricCompatible (I := I) g)
        basis gInvAt hinv
        (fun y : M =>
          inner0S (I := I) g y 1
            (differential1FormFun (I := I) u y)
            (differential1FormFun (I := I) u y))
        normDuSec normSecondSec X hfields hnormDu hnormHess hnormGrad
  refine fundamental_bochner_of_lc (I := I) g Ric Rm13 Rm04
    gInvFrame frame hRm13 hRic13 hRic04 u Hess nablaDu roughDu
    basis gInvAt hinv duSec nablaDuSec nabla2Du normSecond
    hdu hnabla hnabla2 hlapDirect ?_ hrough hdlap hsymm hthird hSkew ?_
  · exact oneForm_norm_second_product_of_metric_compatible (I := I)
      (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) g) g
      basis gInvAt duSec (differential1FormFun (I := I) u) nablaDu
      nablaDuSec nabla2Du normSecond hsecond
  · exact hessian_components_of_nabla_du (I := I)
      (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) g) basis X duSec Hess
      nablaDu hfields hHess hnabla



theorem fundamental_bochner_of_lc_terms_of_rm04_skew
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    [SigmaCompactSpace M] [T2Space M]
    (g : SmoothRiemannianMetric I M)
    (Ric : Tensor02Section (I := I) (M := M))
    (Rm13 : Tensor13Section (I := I) (M := M))
    (Rm04 : Tensor04Section (I := I) (M := M))
    (gInvFrame : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hRm13 : Rm13RealizesConnection (I := I)
      (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) g) Rm13)
    (hRm04 : Rm04RealizesConnection (I := I) g
      (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) g) Rm04)
    (hRic13 : RicciTensorRealizesRm13Trace (I := I) Ric Rm13)
    (hRic04 : RicciTensorRealizesRm04TraceInFrame (I := I) Ric Rm04 gInvFrame frame)
    (u : M -> Real)
    (Hess nablaDu : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (roughDu : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInvAt : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis_gen (I := I) g x basis gInvAt)
    (X : Idx -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (duSec : OneFormSection (I := I) (M := M))
    (nablaDuSec : TwoTensorSection (I := I) (M := M))
    (nabla2Du :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (normSecond :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (hfields : SmoothBasisFieldsAt (I := I) basis X)
    (hHess : HessianRealizesNablaDuAt (I := I)
      (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) g) duSec Hess x)
    (hdu : DuFieldRealizes (I := I) u duSec)
    (hnabla : NablaOneFormRealizesAt (I := I)
      (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) g) duSec nablaDu x)
    (hnabla2 : Nabla2OneFormRealizesAt (I := I)
      (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) g) duSec nablaDuSec x nabla2Du)
    (hlapTrace :
      laplacian (I := I)
        (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) g) g
        (fun y : M =>
          inner0S (I := I) g y 1
            (differential1FormFun (I := I) u y)
            (differential1FormFun (I := I) u y)) x =
        metricTrace0S2InBasis (I := I) basis gInvAt normSecond Fin.elim0)
    (hsecond : OneFormNormSecondProductInBasis (I := I) basis gInvAt
      (differential1FormFun (I := I) u x) (nablaDu x) nabla2Du normSecond)
    (hrough : RoughLap0SRealizesMetricTrace (I := I) g (s := 1) (roughDu x) nabla2Du)
    (hdlap : TraceNablaHessianRealizesDLapAt (I := I)
      (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) g) g u nabla2Du)
    (hsymm : OneFormLastTwoSymmAt (I := I) nabla2Du)
    (hthird : OneFormThirdCovDerivCommAt (I := I) Rm13
      (differential1FormFun (I := I) u x) nabla2Du)
    (hRm04Skew : Rm04OutputSkewAt (I := I) (Rm04 x)) :
    (1 / 2 : Real) * laplacian (I := I)
        (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) g) g
        (gradNormSq (I := I) g u) x =
      g.inner x
          (gradientFun (I := I) g
            (laplacian (I := I)
              (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) g) g u) x)
          (gradientFun (I := I) g u x) +
        hessianNormSq (I := I) g Hess x +
          ricciGradGrad (I := I) Ric g u x := by
  refine fundamental_bochner_of_lc_terms (I := I) g Ric Rm13 Rm04
    gInvFrame frame hRm13 hRic13 hRic04 u Hess nablaDu roughDu
    basis gInvAt hinv X duSec nablaDuSec nabla2Du normSecond
    hfields hHess hdu hnabla hnabla2 hlapTrace hsecond hrough hdlap
    hsymm hthird ?_
  exact rm13MetricSkewAt_of_realizes_outputSkew (I := I) g
    (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) g) Rm13 Rm04
    hRm13 hRm04 hRm04Skew

end DifferentialGeometry.Integral.Connection
