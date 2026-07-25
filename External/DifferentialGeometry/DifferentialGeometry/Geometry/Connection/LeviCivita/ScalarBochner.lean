import DifferentialGeometry.Geometry.Curvature.Bochner.ScalarBochner
import DifferentialGeometry.Geometry.Connection.LeviCivita.Curvature.LeviCivita
import DifferentialGeometry.Geometry.Connection.LeviCivita.Curvature.Realized
import DifferentialGeometry.Geometry.Connection.LeviCivita.Hessian

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false








noncomputable section

namespace DifferentialGeometry.Integral.Connection

open Bundle Tensor0SBundle
open DifferentialGeometry.Integral.Connection
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M]




omit [IsManifold I ∞ M] in
theorem nabla2OneFormRealizesAt_of_totalNabla_leviCivita
    [IsManifold I ∞ M]
    [SigmaCompactSpace M] [T2Space M]
    (g : SmoothRiemannianMetric I M)
    (alpha : OneFormSection (I := I) (M := M))
    (nablaAlpha : TwoTensorSection (I := I) (M := M))
    (nabla2AlphaSec :
      Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) 3)
    (h1 : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 1 (leviCivitaConnectionOfMetric (I := I) g)
      alpha nablaAlpha)
    (h2 : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 2 (leviCivitaConnectionOfMetric (I := I) g)
      nablaAlpha nabla2AlphaSec)
    (x : M) :
    Nabla2OneFormRealizesAt (I := I)
      (leviCivitaConnectionOfMetric (I := I) g) alpha nablaAlpha x
      (nabla2AlphaSec x) :=
  nabla2OneFormRealizesAt_of_totalNabla (I := I)
    (leviCivitaConnectionOfMetric (I := I) g) alpha nablaAlpha
    nabla2AlphaSec h1 h2 x








omit [IsManifold I ∞ M] in
theorem traceNablaHessianRealizesDLapAt_of_leviCivita
    [IsManifold I ∞ M]
    [SigmaCompactSpace M] [T2Space M]
    (g : SmoothRiemannianMetric I M) (u : M -> Real)
    (nablaDuSec : TwoTensorSection (I := I) (M := M))
    (nabla2DuSec :
      Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) 3)
    (hnabla : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I)
      (M := M) 2 (leviCivitaConnectionOfMetric (I := I) g)
      nablaDuSec nabla2DuSec)
    (htrace : ∀ y : M,
      laplacian (I := I) (leviCivitaConnectionOfMetric (I := I) g) g u y =
        scalarLapTraceAt (I := I) g (nablaDuSec y))
    (x : M) :
    TraceNablaHessianRealizesDLapAt (I := I)
      (leviCivitaConnectionOfMetric (I := I) g) g u (nabla2DuSec x) :=
  traceNablaHessianRealizesDLapAt_of_lapTrace (I := I)
    (leviCivitaConnectionOfMetric (I := I) g) g
    (leviCivitaConnectionOfMetric_isMetricCompatible (I := I) g)
    u nablaDuSec nabla2DuSec hnabla htrace x



omit [IsManifold I ∞ M] in
theorem lc_lapTrace
    [IsManifold I ∞ M]
    [SigmaCompactSpace M] [T2Space M]
    (g : SmoothRiemannianMetric I M) (u : M -> Real)
    (duSec : OneFormSection (I := I) (M := M))
    (nablaDuSec : TwoTensorSection (I := I) (M := M))
    (hdu : DuFieldRealizes (I := I) u duSec)
    (hnabla : NablaOneFormSectionRealizes (I := I)
      (leviCivitaConnectionOfMetric (I := I) g) duSec nablaDuSec)
    (hgrad : ∀ y : M,
      MDiffAt (T% fun z : M => gradientFun (I := I) g u z) y) :
    ∀ y : M,
      laplacian (I := I) (leviCivitaConnectionOfMetric (I := I) g) g u y =
        scalarLapTraceAt (I := I) g (nablaDuSec y) := by
  refine lapTrace_nablaSec (I := I)
    (leviCivitaConnectionOfMetric (I := I) g) g
    (leviCivitaConnectionOfMetric_isMetricCompatible (I := I) g)
    u duSec (fun y : M => nablaDuSec y) hdu ?_ hgrad
  intro y
  exact hess_of_nabla (I := I)
    (leviCivitaConnectionOfMetric (I := I) g) duSec
    (fun z : M => nablaDuSec z) y (hnabla y)



omit [IsManifold I ∞ M] in
theorem fundamental_bochner_of_leviCivita_terms
    [IsManifold I ∞ M]
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    [SigmaCompactSpace M] [T2Space M]
    (g : SmoothRiemannianMetric I M)
    (Ric : Tensor02Section (I := I) (M := M))
    (Rm13 : Tensor13Section (I := I) (M := M))
    (Rm04 : Tensor04Section (I := I) (M := M))
    (gInvFrame : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hRm13 : Rm13RealizesConnection (I := I)
      (leviCivitaConnectionOfMetric (I := I) g) Rm13)
    (hRm04 : Rm04RealizesConnection (I := I) g
      (leviCivitaConnectionOfMetric (I := I) g) Rm04)
    (hRic13 : RicciTensorRealizesRm13Trace (I := I) Ric Rm13)
    (hRic04 : RicciTensorRealizesRm04TraceInFrame (I := I) Ric Rm04 gInvFrame frame)
    (u : M -> Real)
    (hu : ContMDiff I 𝓘(Real, Real) ∞ u)
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
      (leviCivitaConnectionOfMetric (I := I) g) duSec Hess x)
    (hdu : DuFieldRealizes (I := I) u duSec)
    (hnabla : NablaOneFormRealizesAt (I := I)
      (leviCivitaConnectionOfMetric (I := I) g) duSec nablaDu x)
    (hnabla2 : Nabla2OneFormRealizesAt (I := I)
      (leviCivitaConnectionOfMetric (I := I) g) duSec nablaDuSec x nabla2Du)
    (hdlap : TraceNablaHessianRealizesDLapAt (I := I)
      (leviCivitaConnectionOfMetric (I := I) g) g u nabla2Du)
    (hlapTrace :
      laplacian (I := I)
        (leviCivitaConnectionOfMetric (I := I) g) g
        (fun y : M =>
          inner0S (I := I) g y 1
            (differential1FormFun (I := I) u y)
            (differential1FormFun (I := I) u y)) x =
        metricTrace0S2InBasis (I := I) basis gInvAt normSecond Fin.elim0)
    (hsecond : OneFormNormSecondProductInBasis (I := I) basis gInvAt
      (differential1FormFun (I := I) u x) (nablaDu x) nabla2Du normSecond)
    (hrough : RoughLap0SRealizesMetricTrace (I := I) g (s := 1) (roughDu x) nabla2Du) :
    (1 / 2 : Real) * laplacian (I := I)
        (leviCivitaConnectionOfMetric (I := I) g) g
        (gradNormSq (I := I) g u) x =
      g.inner x
          (gradientFun (I := I) g
            (laplacian (I := I)
              (leviCivitaConnectionOfMetric (I := I) g) g u) x)
          (gradientFun (I := I) g u x) +
        hessianNormSq (I := I) g Hess x +
          ricciGradGrad (I := I) Ric g u x := by
  refine fundamental_bochner_of_lc_terms (I := I) g Ric Rm13 Rm04
    gInvFrame frame hRm13 hRic13 hRic04 u Hess nablaDu roughDu
    basis gInvAt hinv X duSec nablaDuSec nabla2Du normSecond
    hfields hHess hdu hnabla hnabla2 hlapTrace hsecond hrough hdlap ?_ ?_ ?_
  · exact oneFormLastTwoSymmAt_of_leviCivita_du (I := I)
      g u hu duSec nablaDuSec nabla2Du hdu hnabla2
  · exact oneFormThirdCovDerivCommAt_of_leviCivita (I := I)
      g Rm13 duSec nablaDuSec (differential1FormFun (I := I) u x)
      nabla2Du hRm13 (by simpa [duField] using hdu x) hnabla2
  · exact rm13MetricSkewAt_of_leviCivita_realizes (I := I)
      g Rm13 Rm04 hRm13 hRm04



omit [IsManifold I ∞ M] in
theorem fundamental_bochner_of_leviCivita_terms_of_normSecond_realizes
    [IsManifold I ∞ M]
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    [SigmaCompactSpace M] [T2Space M]
    (g : SmoothRiemannianMetric I M)
    (Ric : Tensor02Section (I := I) (M := M))
    (Rm13 : Tensor13Section (I := I) (M := M))
    (Rm04 : Tensor04Section (I := I) (M := M))
    (gInvFrame : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hRm13 : Rm13RealizesConnection (I := I)
      (leviCivitaConnectionOfMetric (I := I) g) Rm13)
    (hRm04 : Rm04RealizesConnection (I := I) g
      (leviCivitaConnectionOfMetric (I := I) g) Rm04)
    (hRic13 : RicciTensorRealizesRm13Trace (I := I) Ric Rm13)
    (hRic04 : RicciTensorRealizesRm04TraceInFrame (I := I) Ric Rm04 gInvFrame frame)
    (u : M -> Real)
    (hu : ContMDiff I 𝓘(Real, Real) ∞ u)
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
      (leviCivitaConnectionOfMetric (I := I) g) duSec Hess x)
    (hdu : DuFieldRealizes (I := I) u duSec)
    (hnabla : NablaOneFormRealizesAt (I := I)
      (leviCivitaConnectionOfMetric (I := I) g) duSec nablaDu x)
    (hnabla2 : Nabla2OneFormRealizesAt (I := I)
      (leviCivitaConnectionOfMetric (I := I) g) duSec nablaDuSec x nabla2Du)
    (hdlap : TraceNablaHessianRealizesDLapAt (I := I)
      (leviCivitaConnectionOfMetric (I := I) g) g u nabla2Du)
    (hnormSecond : normSecondSec x = normSecond)
    (hnormDu : DuFieldRealizes (I := I)
      (fun y : M =>
        inner0S (I := I) g y 1
          (differential1FormFun (I := I) u y)
          (differential1FormFun (I := I) u y)) normDuSec)
    (hnormHess : HessianRealizesNablaDuAt (I := I)
      (leviCivitaConnectionOfMetric (I := I) g) normDuSec normSecondSec x)
    (hnormGrad : MDiffAt (T% fun y : M =>
      gradientFun (I := I) g
        (fun z : M =>
          inner0S (I := I) g z 1
            (differential1FormFun (I := I) u z)
            (differential1FormFun (I := I) u z)) y) x)
    (hsecond : OneFormNormSecondProductInBasis (I := I) basis gInvAt
      (differential1FormFun (I := I) u x) (nablaDu x) nabla2Du normSecond)
    (hrough : RoughLap0SRealizesMetricTrace (I := I) g (s := 1) (roughDu x) nabla2Du) :
    (1 / 2 : Real) * laplacian (I := I)
        (leviCivitaConnectionOfMetric (I := I) g) g
        (gradNormSq (I := I) g u) x =
      g.inner x
          (gradientFun (I := I) g
            (laplacian (I := I)
              (leviCivitaConnectionOfMetric (I := I) g) g u) x)
          (gradientFun (I := I) g u x) +
        hessianNormSq (I := I) g Hess x +
          ricciGradGrad (I := I) Ric g u x := by
  refine fundamental_bochner_of_lc_terms_of_normSecond_realizes (I := I)
    g Ric Rm13 Rm04 gInvFrame frame hRm13 hRic13 hRic04
    u Hess nablaDu roughDu basis gInvAt hinv X duSec normDuSec
    nablaDuSec nabla2Du normSecond normSecondSec hfields hHess hdu
    hnabla hnabla2 hnormSecond hnormDu hnormHess hnormGrad hsecond hrough
    hdlap ?_ ?_ ?_
  · exact oneFormLastTwoSymmAt_of_leviCivita_du (I := I)
      g u hu duSec nablaDuSec nabla2Du hdu hnabla2
  · exact oneFormThirdCovDerivCommAt_of_leviCivita (I := I)
      g Rm13 duSec nablaDuSec (differential1FormFun (I := I) u x)
      nabla2Du hRm13 (by simpa [duField] using hdu x) hnabla2
  · exact rm13MetricSkewAt_of_leviCivita_realizes (I := I)
      g Rm13 Rm04 hRm13 hRm04








omit [IsManifold I ∞ M] in
theorem lc_bochner_dlap
    [IsManifold I ∞ M]
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    [SigmaCompactSpace M] [T2Space M]
    (g : SmoothRiemannianMetric I M)
    (Ric : Tensor02Section (I := I) (M := M))
    (Rm13 : Tensor13Section (I := I) (M := M))
    (Rm04 : Tensor04Section (I := I) (M := M))
    (gInvFrame : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hRm13 : Rm13RealizesConnection (I := I)
      (leviCivitaConnectionOfMetric (I := I) g) Rm13)
    (hRm04 : Rm04RealizesConnection (I := I) g
      (leviCivitaConnectionOfMetric (I := I) g) Rm04)
    (hRic13 : RicciTensorRealizesRm13Trace (I := I) Ric Rm13)
    (hRic04 : RicciTensorRealizesRm04TraceInFrame (I := I) Ric Rm04 gInvFrame frame)
    (u : M -> Real)
    (hu : ContMDiff I 𝓘(Real, Real) ∞ u)
    (roughDu : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInvAt : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis_gen (I := I) g x basis gInvAt)
    (X : Idx -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (duSec : OneFormSection (I := I) (M := M))
    (nablaDuSec : TwoTensorSection (I := I) (M := M))
    (nabla2DuSec :
      Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) 3)
    (normSecond :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (hfields : SmoothBasisFieldsAt (I := I) basis X)
    (hdu : DuFieldRealizes (I := I) u duSec)
    (hnabla2 : Nabla2OneFormRealizesAt (I := I)
      (leviCivitaConnectionOfMetric (I := I) g) duSec nablaDuSec x
        (nabla2DuSec x))
    (hnablaTrace : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 2 (leviCivitaConnectionOfMetric (I := I) g)
      nablaDuSec nabla2DuSec)
    (hnablaSec : NablaOneFormSectionRealizes (I := I)
      (leviCivitaConnectionOfMetric (I := I) g) duSec nablaDuSec)
    (hgradU : ∀ y : M,
      MDiffAt (T% fun z : M => gradientFun (I := I) g u z) y)
    (hlapTrace :
      laplacian (I := I)
        (leviCivitaConnectionOfMetric (I := I) g) g
        (fun y : M =>
          inner0S (I := I) g y 1
            (differential1FormFun (I := I) u y)
            (differential1FormFun (I := I) u y)) x =
        metricTrace0S2InBasis (I := I) basis gInvAt normSecond Fin.elim0)
    (hsecond : OneFormNormSecondProductInBasis (I := I) basis gInvAt
      (differential1FormFun (I := I) u x) (nablaDuSec x)
        (nabla2DuSec x) normSecond)
    (hrough : RoughLap0SRealizesMetricTrace (I := I) g (s := 1) (roughDu x)
      (nabla2DuSec x)) :
    (1 / 2 : Real) * laplacian (I := I)
        (leviCivitaConnectionOfMetric (I := I) g) g
        (gradNormSq (I := I) g u) x =
      g.inner x
          (gradientFun (I := I) g
            (laplacian (I := I)
              (leviCivitaConnectionOfMetric (I := I) g) g u) x)
          (gradientFun (I := I) g u x) +
        hessianNormSq (I := I) g (fun y : M => nablaDuSec y) x +
          ricciGradGrad (I := I) Ric g u x := by
  have hnablaLocal : NablaOneFormRealizesAt (I := I)
      (leviCivitaConnectionOfMetric (I := I) g) duSec
      (fun y : M => nablaDuSec y) x := hnablaSec x
  have hHessLocal : HessianRealizesNablaDuAt (I := I)
      (leviCivitaConnectionOfMetric (I := I) g) duSec
      (fun y : M => nablaDuSec y) x :=
    hess_of_nabla (I := I)
      (leviCivitaConnectionOfMetric (I := I) g) duSec
      (fun y : M => nablaDuSec y) x hnablaLocal
  have hlapU : ∀ y : M,
      laplacian (I := I) (leviCivitaConnectionOfMetric (I := I) g) g u y =
        scalarLapTraceAt (I := I) g (nablaDuSec y) :=
    lc_lapTrace (I := I) g u duSec nablaDuSec hdu hnablaSec hgradU
  have hdlap : TraceNablaHessianRealizesDLapAt (I := I)
      (leviCivitaConnectionOfMetric (I := I) g) g u (nabla2DuSec x) :=
    traceNablaHessianRealizesDLapAt_of_leviCivita (I := I) g u
      nablaDuSec nabla2DuSec hnablaTrace hlapU x
  exact fundamental_bochner_of_leviCivita_terms (I := I) g Ric Rm13
    Rm04 gInvFrame frame hRm13 hRm04 hRic13 hRic04 u hu
    (fun y : M => nablaDuSec y) (fun y : M => nablaDuSec y)
    roughDu basis gInvAt hinv X duSec nablaDuSec (nabla2DuSec x) normSecond
    hfields hHessLocal hdu hnablaLocal hnabla2 hdlap hlapTrace hsecond hrough



omit [IsManifold I ∞ M] in
theorem lc_bochner_norm
    [IsManifold I ∞ M]
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    [SigmaCompactSpace M] [T2Space M]
    (g : SmoothRiemannianMetric I M)
    (Ric : Tensor02Section (I := I) (M := M))
    (Rm13 : Tensor13Section (I := I) (M := M))
    (Rm04 : Tensor04Section (I := I) (M := M))
    (gInvFrame : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hRm13 : Rm13RealizesConnection (I := I)
      (leviCivitaConnectionOfMetric (I := I) g) Rm13)
    (hRm04 : Rm04RealizesConnection (I := I) g
      (leviCivitaConnectionOfMetric (I := I) g) Rm04)
    (hRic13 : RicciTensorRealizesRm13Trace (I := I) Ric Rm13)
    (hRic04 : RicciTensorRealizesRm04TraceInFrame (I := I) Ric Rm04 gInvFrame frame)
    (u : M -> Real)
    (hu : ContMDiff I 𝓘(Real, Real) ∞ u)
    (roughDu : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInvAt : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis_gen (I := I) g x basis gInvAt)
    (X : Idx -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (duSec normDuSec : OneFormSection (I := I) (M := M))
    (nablaDuSec : TwoTensorSection (I := I) (M := M))
    (nabla2DuSec :
      Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) 3)
    (normSecond :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (normSecondSec : (y : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 y)
    (hfields : SmoothBasisFieldsAt (I := I) basis X)
    (hdu : DuFieldRealizes (I := I) u duSec)
    (hnabla2 : Nabla2OneFormRealizesAt (I := I)
      (leviCivitaConnectionOfMetric (I := I) g) duSec nablaDuSec x
        (nabla2DuSec x))
    (hnablaTrace : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 2 (leviCivitaConnectionOfMetric (I := I) g)
      nablaDuSec nabla2DuSec)
    (hnablaSec : NablaOneFormSectionRealizes (I := I)
      (leviCivitaConnectionOfMetric (I := I) g) duSec nablaDuSec)
    (hgradU : ∀ y : M,
      MDiffAt (T% fun z : M => gradientFun (I := I) g u z) y)
    (hnormSecond : normSecondSec x = normSecond)
    (hnormDu : DuFieldRealizes (I := I)
      (fun y : M =>
        inner0S (I := I) g y 1
          (differential1FormFun (I := I) u y)
          (differential1FormFun (I := I) u y)) normDuSec)
    (hnormHess : HessianRealizesNablaDuAt (I := I)
      (leviCivitaConnectionOfMetric (I := I) g) normDuSec normSecondSec x)
    (hnormGrad : MDiffAt (T% fun y : M =>
      gradientFun (I := I) g
        (fun z : M =>
          inner0S (I := I) g z 1
            (differential1FormFun (I := I) u z)
            (differential1FormFun (I := I) u z)) y) x)
    (hsecond : OneFormNormSecondProductInBasis (I := I) basis gInvAt
      (differential1FormFun (I := I) u x) (nablaDuSec x)
        (nabla2DuSec x) normSecond)
    (hrough : RoughLap0SRealizesMetricTrace (I := I) g (s := 1) (roughDu x)
      (nabla2DuSec x)) :
    (1 / 2 : Real) * laplacian (I := I)
        (leviCivitaConnectionOfMetric (I := I) g) g
        (gradNormSq (I := I) g u) x =
      g.inner x
          (gradientFun (I := I) g
            (laplacian (I := I)
              (leviCivitaConnectionOfMetric (I := I) g) g u) x)
          (gradientFun (I := I) g u x) +
        hessianNormSq (I := I) g (fun y : M => nablaDuSec y) x +
          ricciGradGrad (I := I) Ric g u x := by
  have hnablaLocal : NablaOneFormRealizesAt (I := I)
      (leviCivitaConnectionOfMetric (I := I) g) duSec
      (fun y : M => nablaDuSec y) x := hnablaSec x
  have hHessLocal : HessianRealizesNablaDuAt (I := I)
      (leviCivitaConnectionOfMetric (I := I) g) duSec
      (fun y : M => nablaDuSec y) x :=
    hess_of_nabla (I := I)
      (leviCivitaConnectionOfMetric (I := I) g) duSec
      (fun y : M => nablaDuSec y) x hnablaLocal
  have hlapU : ∀ y : M,
      laplacian (I := I) (leviCivitaConnectionOfMetric (I := I) g) g u y =
        scalarLapTraceAt (I := I) g (nablaDuSec y) :=
    lc_lapTrace (I := I) g u duSec nablaDuSec hdu hnablaSec hgradU
  have hdlap : TraceNablaHessianRealizesDLapAt (I := I)
      (leviCivitaConnectionOfMetric (I := I) g) g u (nabla2DuSec x) :=
    traceNablaHessianRealizesDLapAt_of_leviCivita (I := I) g u
      nablaDuSec nabla2DuSec hnablaTrace hlapU x
  exact fundamental_bochner_of_leviCivita_terms_of_normSecond_realizes
    (I := I) g Ric Rm13 Rm04 gInvFrame frame hRm13 hRm04 hRic13
    hRic04 u hu (fun y : M => nablaDuSec y) (fun y : M => nablaDuSec y)
    roughDu basis gInvAt hinv X duSec normDuSec
    nablaDuSec (nabla2DuSec x) normSecond normSecondSec hfields hHessLocal hdu
    hnablaLocal hnabla2 hdlap hnormSecond hnormDu hnormHess hnormGrad hsecond hrough



omit [IsManifold I ∞ M] in
theorem lc_bochner_rm04
    [IsManifold I ∞ M]
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    [SigmaCompactSpace M] [T2Space M]
    (g : SmoothRiemannianMetric I M)
    (Ric : Tensor02Section (I := I) (M := M))
    (Rm13 : Tensor13Section (I := I) (M := M))
    (Rm04 : Tensor04Section (I := I) (M := M))
    (gInvFrame : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hRm13 : Rm13RealizesConnection (I := I)
      (leviCivitaConnectionOfMetric (I := I) g) Rm13)
    (hRm04 : Rm04RealizesConnection (I := I) g
      (leviCivitaConnectionOfMetric (I := I) g) Rm04)
    (hRic13 : RicciTensorRealizesRm13Trace (I := I) Ric Rm13)
    (hRic04 : RicciTensorRealizesRm04TraceInFrame (I := I) Ric Rm04 gInvFrame frame)
    (u : M -> Real)
    (hu : ContMDiff I 𝓘(Real, Real) ∞ u)
    (roughDu : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInvAt : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis_gen (I := I) g x basis gInvAt)
    (X : Idx -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (duSec : OneFormSection (I := I) (M := M))
    (nablaDuSec : TwoTensorSection (I := I) (M := M))
    (nabla2DuSec :
      Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) 3)
    (normSecond :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (hfields : SmoothBasisFieldsAt (I := I) basis X)
    (hdu : DuFieldRealizes (I := I) u duSec)
    (hnabla2 : Nabla2OneFormRealizesAt (I := I)
      (leviCivitaConnectionOfMetric (I := I) g) duSec nablaDuSec x
        (nabla2DuSec x))
    (hnablaTrace : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 2 (leviCivitaConnectionOfMetric (I := I) g)
      nablaDuSec nabla2DuSec)
    (hnablaSec : NablaOneFormSectionRealizes (I := I)
      (leviCivitaConnectionOfMetric (I := I) g) duSec nablaDuSec)
    (hgradU : ∀ y : M,
      MDiffAt (T% fun z : M => gradientFun (I := I) g u z) y)
    (hlapTrace :
      laplacian (I := I)
        (leviCivitaConnectionOfMetric (I := I) g) g
        (fun y : M =>
          inner0S (I := I) g y 1
            (differential1FormFun (I := I) u y)
            (differential1FormFun (I := I) u y)) x =
        metricTrace0S2InBasis (I := I) basis gInvAt normSecond Fin.elim0)
    (hsecond : OneFormNormSecondProductInBasis (I := I) basis gInvAt
      (differential1FormFun (I := I) u x) (nablaDuSec x)
        (nabla2DuSec x) normSecond)
    (hrough : RoughLap0SRealizesMetricTrace (I := I) g (s := 1) (roughDu x)
      (nabla2DuSec x))
    (hRm04Skew : Rm04OutputSkewAt (I := I) (Rm04 x)) :
    (1 / 2 : Real) * laplacian (I := I)
        (leviCivitaConnectionOfMetric (I := I) g) g
        (gradNormSq (I := I) g u) x =
      g.inner x
          (gradientFun (I := I) g
            (laplacian (I := I)
              (leviCivitaConnectionOfMetric (I := I) g) g u) x)
          (gradientFun (I := I) g u x) +
        hessianNormSq (I := I) g (fun y : M => nablaDuSec y) x +
          ricciGradGrad (I := I) Ric g u x := by
  have hnablaLocal : NablaOneFormRealizesAt (I := I)
      (leviCivitaConnectionOfMetric (I := I) g) duSec
      (fun y : M => nablaDuSec y) x := hnablaSec x
  have hHessLocal : HessianRealizesNablaDuAt (I := I)
      (leviCivitaConnectionOfMetric (I := I) g) duSec
      (fun y : M => nablaDuSec y) x :=
    hess_of_nabla (I := I)
      (leviCivitaConnectionOfMetric (I := I) g) duSec
      (fun y : M => nablaDuSec y) x hnablaLocal
  have hlapU : ∀ y : M,
      laplacian (I := I) (leviCivitaConnectionOfMetric (I := I) g) g u y =
        scalarLapTraceAt (I := I) g (nablaDuSec y) :=
    lc_lapTrace (I := I) g u duSec nablaDuSec hdu hnablaSec hgradU
  have hdlap : TraceNablaHessianRealizesDLapAt (I := I)
      (leviCivitaConnectionOfMetric (I := I) g) g u (nabla2DuSec x) :=
    traceNablaHessianRealizesDLapAt_of_leviCivita (I := I) g u
      nablaDuSec nabla2DuSec hnablaTrace hlapU x
  have hsymm : OneFormLastTwoSymmAt (I := I) (nabla2DuSec x) :=
    oneFormLastTwoSymmAt_of_leviCivita_du (I := I)
      g u hu duSec nablaDuSec (nabla2DuSec x) hdu hnabla2
  have hthird : OneFormThirdCovDerivCommAt (I := I) Rm13
      (differential1FormFun (I := I) u x) (nabla2DuSec x) :=
    oneFormThirdCovDerivCommAt_of_leviCivita (I := I)
      g Rm13 duSec nablaDuSec (differential1FormFun (I := I) u x)
      (nabla2DuSec x) hRm13 (by simpa [duField] using hdu x) hnabla2
  exact DifferentialGeometry.Integral.Connection.fundamental_bochner_of_lc_terms_of_rm04_skew (I := I)
    g Ric Rm13 Rm04 gInvFrame frame hRm13 hRm04 hRic13 hRic04 u
    (fun y : M => nablaDuSec y) (fun y : M => nablaDuSec y)
    roughDu basis gInvAt hinv X duSec nablaDuSec (nabla2DuSec x)
    normSecond hfields hHessLocal hdu hnablaLocal hnabla2 hlapTrace hsecond hrough
    hdlap hsymm hthird hRm04Skew

end DifferentialGeometry.Integral.Connection
