import DifferentialGeometry.Geometry.Coordinates.Christoffel
import DifferentialGeometry.Geometry.Coordinates.ChristoffelTensor
import DifferentialGeometry.Geometry.Coordinates.MetricCompatibility.Inverse
import DifferentialGeometry.Geometry.Coordinates.MetricCompatibility.Covariant
import DifferentialGeometry.Geometry.Coordinates.MetricCompatibility.Coordinate
import DifferentialGeometry.Geometry.Curvature.Basic
import DifferentialGeometry.Geometry.Curvature.Components.Basic
import DifferentialGeometry.Geometry.Curvature.Components.Lowering
import DifferentialGeometry.Geometry.Curvature.Components.TraceOneForm
import DifferentialGeometry.Geometry.Curvature.Components.RicciTrace
import DifferentialGeometry.Geometry.Curvature.Components.LocalFrame
import DifferentialGeometry.Geometry.Curvature.Components.Christoffel
import DifferentialGeometry.Geometry.Curvature.Components.RicciIdentity
import DifferentialGeometry.Geometry.Connection.LeviCivita.Basic
import DifferentialGeometry.Geometry.Connection.LeviCivita.Torsion
import DifferentialGeometry.Geometry.Connection.Variation.Basic
import DifferentialGeometry.Bundle.PartialMfderiv.Basic
import DifferentialGeometry.Bundle.PartialMfderiv.ModelMixed
import DifferentialGeometry.Bundle.PartialMfderiv.FixedBase

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

noncomputable section

namespace DifferentialGeometry.Integral.Connection

open Bundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
variable {Idx : Type*} [Fintype Idx]
variable {u : Set M}







variable {u : Set M}


def connDiffVec
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (base var : Real) (x : M) (i j : Idx) : TangentSpace I x :=
  (G.connection var (frame j) x) (frame i x) -
    (G.connection base (frame j) x) (frame i x)


def connDiffLow
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (metricTime base var : Real) (x : M) (i j l : Idx) : Real :=
  (G.metric metricTime).inner x
    (connDiffVec (I := I) G frame base var x i j) (frame l x)

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [Fintype Idx] in
@[simp] theorem connDiffVec_self
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (base : Real) (x : M) (i j : Idx) :
    connDiffVec (I := I) G frame base base x i j = 0 := by
  simp [connDiffVec]

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [Fintype Idx] in
@[simp] theorem connDiffLow_self
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (metricTime base : Real) (x : M) (i j l : Idx) :
    connDiffLow (I := I) G frame metricTime base base x i j l = 0 := by
  simp [connDiffLow]




def metricCovAtBase
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (base var : Real) (x : M) (d a b : Idx) : Real :=
  extDerivFun (I := I)
      (fun y : M => (G.metric var).inner y (frame a y) (frame b y))
      x (frame d x) -
    (G.metric var).inner x
      ((G.connection base (frame a) x) (frame d x)) (frame b x) -
    (G.metric var).inner x (frame a x)
      ((G.connection base (frame b) x) (frame d x))



def metricVarLowerRHS
    (metricCovDerivDt : M -> Idx -> Idx -> Idx -> Real)
    (x : M) (i j l : Idx) : Real :=
  (1 / 2 : Real) *
    (metricCovDerivDt x i j l + metricCovDerivDt x j i l -
      metricCovDerivDt x l i j)



def metricVarGammaRHS
    (gInv : DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (metricCovDerivDt : M -> Idx -> Idx -> Idx -> Real)
    (x : M) (i j k : Idx) : Real :=
  ∑ l : Idx, gInv x k l * metricVarLowerRHS metricCovDerivDt x i j l



def metricTraceCovAt
    (gInv : DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (metricCovDerivDt : M -> Idx -> Idx -> Idx -> Real)
    (x : M) (j : Idx) : Real :=
  ∑ p : Idx, ∑ l : Idx, gInv x p l * metricCovDerivDt x j p l



def metricCovVarOn
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (base : Real) (u : Set M)
    (metricCovDerivDt : M -> Idx -> Idx -> Idx -> Real) : Prop :=
  ∀ x : M, x ∈ u -> ∀ d a b : Idx,
    HasDerivAt
      (fun s : Real => metricCovAtBase (I := I) G frame base s x d a b)
      (metricCovDerivDt x d a b)
      base



omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [Fintype Idx] in
theorem metricCovAtBase_symm
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (base var : Real) (x : M) (d a b : Idx) :
    metricCovAtBase (I := I) G frame base var x d a b =
      metricCovAtBase (I := I) G frame base var x d b a := by
  unfold metricCovAtBase
  have hfun :
      (fun y : M => (G.metric var).inner y (frame a y) (frame b y)) =
        fun y : M => (G.metric var).inner y (frame b y) (frame a y) := by
    funext y
    exact (G.metric var).symm y (frame a y) (frame b y)
  rw [hfun]
  rw [(G.metric var).symm x
    ((G.connection base (frame b) x) (frame d x)) (frame a x)]
  rw [(G.metric var).symm x
    (frame b x) ((G.connection base (frame a) x) (frame d x))]
  ring



omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [Fintype Idx] in
theorem metricCovVar_symm
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (base : Real) (u : Set M)
    (metricCovDerivDt : M -> Idx -> Idx -> Idx -> Real)
    (hmetric :
      metricCovVarOn (I := I) G frame base u metricCovDerivDt) :
    ∀ x : M, x ∈ u -> ∀ d a b : Idx,
      metricCovDerivDt x d a b = metricCovDerivDt x d b a := by
  intro x hx d a b
  have h₁ := hmetric x hx d a b
  have h₂ := hmetric x hx d b a
  have hEq :
      (fun s : Real => metricCovAtBase (I := I) G frame base s x d a b) =ᶠ[nhds base]
        fun s : Real => metricCovAtBase (I := I) G frame base s x d b a := by
    exact Filter.Eventually.of_forall fun s =>
      metricCovAtBase_symm (I := I) G frame base s x d a b
  exact h₁.unique (h₂.congr_of_eventuallyEq hEq)


def metricVarOn
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (base : Real) (u : Set M)
    (metricDot : M -> Idx -> Idx -> Real) : Prop :=
  ∀ x : M, x ∈ u -> ∀ a b : Idx,
    HasDerivAt
      (fun s : Real => (G.metric s).inner x (frame a x) (frame b x))
      (metricDot x a b)
      base


def metricDotFrame
    (metricVariation :
      Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (x : M) (a b : Idx) : Real :=
  DifferentialGeometry.Integral.Connection.metricVariationComponent (I := I) metricVariation x
    (frame a x) (frame b x)



omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [Fintype Idx] in
theorem metricVar_path
    {g : SmoothRiemannianMetric I M} {potential : M -> Real}
    (path : DifferentialGeometry.Integral.Connection.MetricPotentialVariationPath (I := I) g potential)
    (metricVariation :
      Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (potentialVariation : M -> Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (u : Set M)
    (hpath :
      DifferentialGeometry.Integral.Connection.IsMetricPotentialVariationPath (I := I) path metricVariation
        potentialVariation) :
    metricVarOn (I := I) path.G frame path.base u
      (metricDotFrame (I := I) metricVariation frame) := by
  intro x _hx a b
  simpa [metricDotFrame] using
    hpath.metric_deriv x (frame a x) (frame b x)




def metricExtDtOn
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (base : Real) (u : Set M)
    (metricDot : M -> Idx -> Idx -> Real) : Prop :=
  ∀ x : M, x ∈ u -> ∀ d a b : Idx,
    HasDerivAt
      (fun s : Real =>
        extDerivFun (I := I)
          (fun y : M => (G.metric s).inner y (frame a y) (frame b y))
          x (frame d x))
      (extDerivFun (I := I) (fun y : M => metricDot y a b) x (frame d x))
      base







omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [Fintype Idx] in
theorem metricExtDt_of_fixedBase
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (base : Real) (u : Set M)
    (metricDot : M -> Idx -> Idx -> Real)
    (hmix : ∀ a b : Idx,
      FixedBaseExtDerivTimeDerivativeOn (I := I) (Set.univ : Set Real) u
        (fun s : Real => fun y : M =>
          (G.metric s).inner y (frame a y) (frame b y))
        (fun _s : Real => fun y : M => metricDot y a b)) :
    metricExtDtOn (I := I) G frame base u metricDot := by
  intro x hx d a b
  have h :=
    fixedBaseExtDerivTimeDerivativeOn_apply (I := I) (h := hmix a b)
      (t := base) (x := x) hx (frame d x)
  simpa using h




omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [Fintype Idx] in
theorem metricExtDt_of_fixedBaseRegular
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (base : Real) (u : Set M)
    (metricDot : M -> Idx -> Idx -> Real)
    (hmix : ∀ a b : Idx,
      FixedBaseExtDerivTimeDerivativeOnRegular (I := I)
        (Set.univ : Set Real) ({base} : Set Real) u
        (fun s : Real => fun y : M =>
          (G.metric s).inner y (frame a y) (frame b y))
        (fun _s : Real => fun y : M => metricDot y a b)) :
    metricExtDtOn (I := I) G frame base u metricDot := by
  intro x hx d a b
  have ht : base ∈ ({base} : Set Real) := by simp
  have h :=
    fixedBaseExtDerivTimeDerivativeOnRegular_apply (I := I)
      (h := hmix a b) (t := base) ht (x := x) hx (frame d x)
  simpa using h



def dotCovAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (metricDot : M -> Idx -> Idx -> Real)
    (x : M) (d a b : Idx) : Real :=
  extDerivFun (I := I) (fun y : M => metricDot y a b) x (frame d x) -
    (∑ p : Idx,
      DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame cov frame hframe x d a p *
        metricDot x p b) -
    (∑ p : Idx,
      DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame cov frame hframe x d b p *
        metricDot x a p)

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [Fintype Idx] in
private theorem localFrame_mdiffAt
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u) (i : Idx) :
    MDiffAt (T% (frame i)) x :=
  (hframe.contMDiffAt hu hx i).mdifferentiableAt one_ne_zero

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem metricVarConnLeft
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (base : Real)
    (metricDot : M -> Idx -> Idx -> Real)
    (hmetricVar : metricVarOn (I := I) G frame base u metricDot)
    {x : M} (hx : x ∈ u) (d a b : Idx) :
    HasDerivAt
      (fun s : Real =>
        (G.metric s).inner x
          ((G.connection base (frame a) x) (frame d x)) (frame b x))
      (∑ p : Idx,
        DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
            (G.connection base) frame hframe x d a p *
          metricDot x p b)
      base := by
  classical
  let Γ : Idx -> Real := fun p =>
    DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
      (G.connection base) frame hframe x d a p
  have hcov :
      (G.connection base (frame a) x) (frame d x) =
        ∑ p : Idx, Γ p • frame p x := by
    simpa [Γ] using
      hframe.coeff_sum_eq
        (fun y => (G.connection base (frame a) y) (frame d y)) hx
  have hsum :
      HasDerivAt
        (fun s : Real =>
          ∑ p : Idx,
            Γ p * (G.metric s).inner x (frame p x) (frame b x))
        (∑ p : Idx, Γ p * metricDot x p b)
        base := by
    simpa using
      (HasDerivAt.fun_sum
        (u := (Finset.univ : Finset Idx))
        (A := fun p s =>
          Γ p * (G.metric s).inner x (frame p x) (frame b x))
        (A' := fun p => Γ p * metricDot x p b)
        (x := base)
        (fun p _hp => by
          simpa using (hmetricVar x hx p b).const_mul (Γ p)))
  have hEq :
      (fun s : Real =>
        (G.metric s).inner x
          ((G.connection base (frame a) x) (frame d x)) (frame b x)) =
        fun s : Real =>
          ∑ p : Idx,
            Γ p * (G.metric s).inner x (frame p x) (frame b x) := by
    funext s
    rw [hcov]
    simp [map_sum, Γ]
  simpa [hEq, Γ] using hsum

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem metricVarConnRight
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (base : Real)
    (metricDot : M -> Idx -> Idx -> Real)
    (hmetricVar : metricVarOn (I := I) G frame base u metricDot)
    {x : M} (hx : x ∈ u) (d a b : Idx) :
    HasDerivAt
      (fun s : Real =>
        (G.metric s).inner x (frame a x)
          ((G.connection base (frame b) x) (frame d x)))
      (∑ p : Idx,
        DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
            (G.connection base) frame hframe x d b p *
          metricDot x a p)
      base := by
  classical
  let Γ : Idx -> Real := fun p =>
    DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
      (G.connection base) frame hframe x d b p
  have hcov :
      (G.connection base (frame b) x) (frame d x) =
        ∑ p : Idx, Γ p • frame p x := by
    simpa [Γ] using
      hframe.coeff_sum_eq
        (fun y => (G.connection base (frame b) y) (frame d y)) hx
  have hsum :
      HasDerivAt
        (fun s : Real =>
          ∑ p : Idx,
            Γ p * (G.metric s).inner x (frame a x) (frame p x))
        (∑ p : Idx, Γ p * metricDot x a p)
        base := by
    simpa using
      (HasDerivAt.fun_sum
        (u := (Finset.univ : Finset Idx))
        (A := fun p s =>
          Γ p * (G.metric s).inner x (frame a x) (frame p x))
        (A' := fun p => Γ p * metricDot x a p)
        (x := base)
        (fun p _hp => by
          simpa using (hmetricVar x hx a p).const_mul (Γ p)))
  have hEq :
      (fun s : Real =>
        (G.metric s).inner x (frame a x)
          ((G.connection base (frame b) x) (frame d x))) =
        fun s : Real =>
          ∑ p : Idx,
            Γ p * (G.metric s).inner x (frame a x) (frame p x) := by
    funext s
    rw [hcov]
    simp [map_sum, Γ]
  simpa [hEq, Γ] using hsum



omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem covDtEqDotCov
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (base : Real)
    (metricDot : M -> Idx -> Idx -> Real)
    (metricCovDerivDt : M -> Idx -> Idx -> Idx -> Real)
    (hmetricVar : metricVarOn (I := I) G frame base u metricDot)
    (hmetric : metricCovVarOn (I := I) G frame base u metricCovDerivDt)
    (hExt : metricExtDtOn (I := I) G frame base u metricDot) :
    ∀ x : M, x ∈ u -> ∀ d a b : Idx,
      metricCovDerivDt x d a b =
        dotCovAt (I := I) (G.connection base) frame hframe metricDot
          x d a b := by
  intro x hx d a b
  let Ca : TangentSpace I x :=
    (G.connection base (frame a) x) (frame d x)
  let Cb : TangentSpace I x :=
    (G.connection base (frame b) x) (frame d x)
  have hDeriv :
      HasDerivAt
        (fun s : Real =>
          extDerivFun (I := I)
              (fun y : M => (G.metric s).inner y (frame a y) (frame b y))
              x (frame d x) -
            (G.metric s).inner x Ca (frame b x) -
            (G.metric s).inner x (frame a x) Cb)
        (dotCovAt (I := I) (G.connection base) frame hframe metricDot
          x d a b)
        base := by
    have hExt' := hExt x hx d a b
    have hCa := metricVarConnLeft
      (I := I) G frame hframe base metricDot hmetricVar hx d a b
    have hCb := metricVarConnRight
      (I := I) G frame hframe base metricDot hmetricVar hx d a b
    have hCa' :
        HasDerivAt
          (fun s : Real => (G.metric s).inner x Ca (frame b x))
          (∑ p : Idx,
            DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
                (G.connection base) frame hframe x d a p *
              metricDot x p b)
          base := by
      simpa [Ca] using hCa
    have hCb' :
        HasDerivAt
          (fun s : Real => (G.metric s).inner x (frame a x) Cb)
          (∑ p : Idx,
            DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
                (G.connection base) frame hframe x d b p *
              metricDot x a p)
          base := by
      simpa [Cb] using hCb
    have h0 := (hExt'.sub hCa').sub hCb'
    refine h0.congr_deriv ?_
    unfold dotCovAt
    ring
  have hDeriv' :
      HasDerivAt
        (fun s : Real => metricCovAtBase (I := I) G frame base s x d a b)
        (dotCovAt (I := I) (G.connection base) frame hframe metricDot
          x d a b)
        base := by
    refine hDeriv.congr_of_eventuallyEq ?_
    exact Filter.Eventually.of_forall fun s => by
      simp [metricCovAtBase, Ca, Cb]
  exact (hmetric x hx d a b).unique hDeriv'






omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem metricCovVar_ext
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (base : Real)
    (metricDot : M -> Idx -> Idx -> Real)
    (hmetricVar : metricVarOn (I := I) G frame base u metricDot)
    (hExt : metricExtDtOn (I := I) G frame base u metricDot) :
    metricCovVarOn (I := I) G frame base u
      (dotCovAt (I := I) (G.connection base) frame hframe metricDot) := by
  intro x hx d a b
  let Ca : TangentSpace I x :=
    (G.connection base (frame a) x) (frame d x)
  let Cb : TangentSpace I x :=
    (G.connection base (frame b) x) (frame d x)
  have hDeriv :
      HasDerivAt
        (fun s : Real =>
          extDerivFun (I := I)
              (fun y : M => (G.metric s).inner y (frame a y) (frame b y))
              x (frame d x) -
            (G.metric s).inner x Ca (frame b x) -
            (G.metric s).inner x (frame a x) Cb)
        (dotCovAt (I := I) (G.connection base) frame hframe metricDot
          x d a b)
        base := by
    have hExt' := hExt x hx d a b
    have hCa := metricVarConnLeft
      (I := I) G frame hframe base metricDot hmetricVar hx d a b
    have hCb := metricVarConnRight
      (I := I) G frame hframe base metricDot hmetricVar hx d a b
    have hCa' :
        HasDerivAt
          (fun s : Real => (G.metric s).inner x Ca (frame b x))
          (∑ p : Idx,
            DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
                (G.connection base) frame hframe x d a p *
              metricDot x p b)
          base := by
      simpa [Ca] using hCa
    have hCb' :
        HasDerivAt
          (fun s : Real => (G.metric s).inner x (frame a x) Cb)
          (∑ p : Idx,
            DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
                (G.connection base) frame hframe x d b p *
              metricDot x a p)
          base := by
      simpa [Cb] using hCb
    have h0 := (hExt'.sub hCa').sub hCb'
    refine h0.congr_deriv ?_
    unfold dotCovAt
    ring
  refine hDeriv.congr_of_eventuallyEq ?_
  exact Filter.Eventually.of_forall fun s => by
    simp [metricCovAtBase, Ca, Cb]

omit [Fintype Idx] in
omit [SigmaCompactSpace M] [T2Space M] in
private theorem connDiffVec_symm
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (hLC : ∀ s : Real,
      IsLeviCivita (I := I) (G.connection s) (G.metric s))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u)
    (base var : Real) (i j : Idx) :
    connDiffVec (I := I) G frame base var x i j =
      connDiffVec (I := I) G frame base var x j i := by
  have hfi : MDiffAt (T% (frame i)) x :=
    localFrame_mdiffAt (I := I) frame hframe hu hx i
  have hfj : MDiffAt (T% (frame j)) x :=
    localFrame_mdiffAt (I := I) frame hframe hu hx j
  have hvar_torsion :=
    DifferentialGeometry.Integral.Connection.torsion_free_apply
      (I := I) (hLC var).2 (hX := hfi) (hY := hfj)
  have hbase_torsion :=
    DifferentialGeometry.Integral.Connection.torsion_free_apply
      (I := I) (hLC base).2 (hX := hfi) (hY := hfj)
  have hdiff :
      (G.connection var (frame j) x) (frame i x) -
          (G.connection var (frame i) x) (frame j x) =
        (G.connection base (frame j) x) (frame i x) -
          (G.connection base (frame i) x) (frame j x) := by
    exact hvar_torsion.trans hbase_torsion.symm
  unfold connDiffVec
  apply sub_eq_zero.mp
  calc
    ((G.connection var (frame j) x) (frame i x) -
          (G.connection base (frame j) x) (frame i x)) -
        ((G.connection var (frame i) x) (frame j x) -
          (G.connection base (frame i) x) (frame j x))
        =
      ((G.connection var (frame j) x) (frame i x) -
          (G.connection var (frame i) x) (frame j x)) -
        ((G.connection base (frame j) x) (frame i x) -
          (G.connection base (frame i) x) (frame j x)) := by
        abel
    _ = 0 := by
        rw [hdiff, sub_self]

omit [Fintype Idx] in
omit [SigmaCompactSpace M] [T2Space M] in
private theorem connDiffLow_symm
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (hLC : ∀ s : Real,
      IsLeviCivita (I := I) (G.connection s) (G.metric s))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u)
    (metricTime base var : Real) (i j l : Idx) :
    connDiffLow (I := I) G frame metricTime base var x i j l =
      connDiffLow (I := I) G frame metricTime base var x j i l := by
  unfold connDiffLow
  rw [connDiffVec_symm (I := I) G hLC frame hframe hu hx base var i j]




omit [SigmaCompactSpace M] [T2Space M] [Fintype Idx] in
theorem metricCovAtBase_eq_connDiff
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (hLC : ∀ s : Real,
      IsLeviCivita (I := I) (G.connection s) (G.metric s))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u)
    (base var : Real) (d a b : Idx) :
    metricCovAtBase (I := I) G frame base var x d a b =
      connDiffLow (I := I) G frame var base var x d a b +
        (G.metric var).inner x (frame a x)
          (connDiffVec (I := I) G frame base var x d b) := by
  have hfd : MDiffAt (T% (frame d)) x :=
    localFrame_mdiffAt (I := I) frame hframe hu hx d
  have hfa : MDiffAt (T% (frame a)) x :=
    localFrame_mdiffAt (I := I) frame hframe hu hx a
  have hfb : MDiffAt (T% (frame b)) x :=
    localFrame_mdiffAt (I := I) frame hframe hu hx b
  have hmc :=
    DifferentialGeometry.Integral.Connection.metric_compatible_apply
      (I := I) (hLC var).1 (frame d) (frame a) (frame b) hfd hfa hfb
  unfold metricCovAtBase connDiffLow connDiffVec
  have hmc' :
      extDerivFun (I := I)
          (fun y : M => (G.metric var).inner y (frame a y) (frame b y))
          x (frame d x) =
        (G.metric var).inner x
            ((G.connection var (frame a) x) (frame d x)) (frame b x) +
          (G.metric var).inner x (frame a x)
            ((G.connection var (frame b) x) (frame d x)) := by
    simpa [extDerivFun] using hmc
  rw [hmc']
  simp
  ring



omit [Fintype Idx] in
omit [SigmaCompactSpace M] [T2Space M] in
theorem finiteDiffKoszul
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (hLC : ∀ s : Real,
      IsLeviCivita (I := I) (G.connection s) (G.metric s))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u)
    (base var : Real) (i j l : Idx) :
    2 * connDiffLow (I := I) G frame var base var x i j l =
      metricCovAtBase (I := I) G frame base var x i j l +
        metricCovAtBase (I := I) G frame base var x j i l -
          metricCovAtBase (I := I) G frame base var x l i j := by
  rw [metricCovAtBase_eq_connDiff
    (I := I) G hLC frame hframe hu hx base var i j l]
  rw [metricCovAtBase_eq_connDiff
    (I := I) G hLC frame hframe hu hx base var j i l]
  rw [metricCovAtBase_eq_connDiff
    (I := I) G hLC frame hframe hu hx base var l i j]
  have hji := connDiffLow_symm
    (I := I) G hLC frame hframe hu hx var base var j i l
  have hli := connDiffLow_symm
    (I := I) G hLC frame hframe hu hx var base var l i j
  have hlj := connDiffVec_symm
    (I := I) G hLC frame hframe hu hx base var l j
  have hsym1 :
      (G.metric var).inner x (frame j x)
          (connDiffVec (I := I) G frame base var x i l) =
        connDiffLow (I := I) G frame var base var x i l j := by
    unfold connDiffLow
    exact (G.metric var).symm x (frame j x)
      (connDiffVec (I := I) G frame base var x i l)
  rw [hji, hli, hlj, hsym1]
  ring



omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem connDiffLow_eq_sum_gammaSub [DecidableEq Idx]
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    {x : M} (hx : x ∈ u)
    (metricTime base var : Real) (i j l : Idx) :
    connDiffLow (I := I) G frame metricTime base var x i j l =
      ∑ k : Idx,
        (DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
            (G.connection var) frame hframe x i j k -
          DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
            (G.connection base) frame hframe x i j k) *
          (G.metric metricTime).inner x (frame k x) (frame l x) := by
  let Vvar : TangentSpace I x :=
    (G.connection var (frame j) x) (frame i x)
  let Vbase : TangentSpace I x :=
    (G.connection base (frame j) x) (frame i x)
  have hvar :
      Vvar =
        ∑ k : Idx,
          DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
              (G.connection var) frame hframe x i j k • frame k x := by
    simpa [Vvar, DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame] using
      hframe.coeff_sum_eq
        (fun y : M => (G.connection var (frame j) y) (frame i y)) hx
  have hbase :
      Vbase =
        ∑ k : Idx,
          DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
              (G.connection base) frame hframe x i j k • frame k x := by
    simpa [Vbase, DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame] using
      hframe.coeff_sum_eq
        (fun y : M => (G.connection base (frame j) y) (frame i y)) hx
  have hdiff :
      Vvar - Vbase =
        ∑ k : Idx,
          (DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
              (G.connection var) frame hframe x i j k -
            DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
              (G.connection base) frame hframe x i j k) • frame k x := by
    calc
      Vvar - Vbase =
          (∑ k : Idx,
            DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
                (G.connection var) frame hframe x i j k • frame k x) -
            (∑ k : Idx,
              DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
                  (G.connection base) frame hframe x i j k • frame k x) := by
            rw [hvar, hbase]
      _ = ∑ k : Idx,
            (DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
                (G.connection var) frame hframe x i j k • frame k x -
              DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
                (G.connection base) frame hframe x i j k • frame k x) := by
            rw [Finset.sum_sub_distrib]
      _ = ∑ k : Idx,
            (DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
                (G.connection var) frame hframe x i j k -
              DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
                (G.connection base) frame hframe x i j k) • frame k x := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [sub_smul]
  calc
    connDiffLow (I := I) G frame metricTime base var x i j l =
        (G.metric metricTime).inner x (Vvar - Vbase) (frame l x) := by
          rfl
    _ = (G.metric metricTime).inner x
        (∑ k : Idx,
          (DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
              (G.connection var) frame hframe x i j k -
            DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
              (G.connection base) frame hframe x i j k) • frame k x)
        (frame l x) := by
          rw [hdiff]
    _ = (G.metric metricTime).inner x (frame l x)
        (∑ k : Idx,
          (DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
              (G.connection var) frame hframe x i j k -
            DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
              (G.connection base) frame hframe x i j k) • frame k x) := by
          rw [(G.metric metricTime).symm x]
    _ = ∑ k : Idx,
        (DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
            (G.connection var) frame hframe x i j k -
          DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
            (G.connection base) frame hframe x i j k) *
          (G.metric metricTime).inner x (frame l x) (frame k x) := by
          rw [map_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [map_smul]
          simp [smul_eq_mul]
    _ = ∑ k : Idx,
        (DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
            (G.connection var) frame hframe x i j k -
          DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
            (G.connection base) frame hframe x i j k) *
          (G.metric metricTime).inner x (frame k x) (frame l x) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [(G.metric metricTime).symm x (frame l x) (frame k x)]







omit [SigmaCompactSpace M] [T2Space M] in
theorem metricCov_gammaSub [DecidableEq Idx]
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (hLC : ∀ s : Real,
      IsLeviCivita (I := I) (G.connection s) (G.metric s))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u)
    (base var : Real) (d a b : Idx) :
    metricCovAtBase (I := I) G frame base var x d a b =
      (∑ k : Idx,
        (DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
            (G.connection var) frame hframe x d a k -
          DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
            (G.connection base) frame hframe x d a k) *
          (G.metric var).inner x (frame k x) (frame b x)) +
        (∑ k : Idx,
          (DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
              (G.connection var) frame hframe x d b k -
            DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
              (G.connection base) frame hframe x d b k) *
            (G.metric var).inner x (frame k x) (frame a x)) := by
  rw [metricCovAtBase_eq_connDiff
    (I := I) G hLC frame hframe hu hx base var d a b]
  rw [connDiffLow_eq_sum_gammaSub
    (I := I) G frame hframe hx var base var d a b]
  have hsecond :
      (G.metric var).inner x (frame a x)
          (connDiffVec (I := I) G frame base var x d b) =
        connDiffLow (I := I) G frame var base var x d b a := by
    unfold connDiffLow
    rw [(G.metric var).symm x (frame a x)
      (connDiffVec (I := I) G frame base var x d b)]
  rw [hsecond]
  rw [connDiffLow_eq_sum_gammaSub
    (I := I) G frame hframe hx var base var d b a]







omit [SigmaCompactSpace M] [T2Space M] in
theorem covCombo_gammaSub [DecidableEq Idx]
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (hLC : ∀ s : Real,
      IsLeviCivita (I := I) (G.connection s) (G.metric s))
    (gInv : DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u)
    (base var : Real)
    (hinv :
      DifferentialGeometry.Integral.Connection.InverseMetricComponentsInFrame
        (I := I) (G.metric var) gInv frame)
    (a b e : Idx) :
    (∑ l : Idx, gInv x e l *
      (metricCovAtBase (I := I) G frame base var x a b l +
        metricCovAtBase (I := I) G frame base var x b a l -
          metricCovAtBase (I := I) G frame base var x l a b)) =
      2 *
        (DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
            (G.connection var) frame hframe x a b e -
          DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
            (G.connection base) frame hframe x a b e) := by
  classical
  let D : Idx -> Real := fun k =>
    DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
        (G.connection var) frame hframe x a b k -
      DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
        (G.connection base) frame hframe x a b k
  let H : Idx -> Idx -> Real := fun k l =>
    (G.metric var).inner x (frame k x) (frame l x)
  have hcombo : ∀ l : Idx,
      metricCovAtBase (I := I) G frame base var x a b l +
        metricCovAtBase (I := I) G frame base var x b a l -
          metricCovAtBase (I := I) G frame base var x l a b =
        2 * connDiffLow (I := I) G frame var base var x a b l := by
    intro l
    exact (finiteDiffKoszul (I := I) G hLC frame hframe hu hx base var a b l).symm
  have hconn : ∀ l : Idx,
      connDiffLow (I := I) G frame var base var x a b l =
        ∑ k : Idx, D k * H k l := by
    intro l
    simpa [D, H] using
      connDiffLow_eq_sum_gammaSub
        (I := I) G frame hframe hx var base var a b l
  have hcontract : ∀ k : Idx,
      (∑ l : Idx, gInv x e l * H k l) =
        (if e = k then 1 else 0) := by
    intro k
    calc
      (∑ l : Idx, gInv x e l * H k l)
          = ∑ l : Idx, gInv x e l * H l k := by
              refine Finset.sum_congr rfl fun l _ => ?_
              simp [H, (G.metric var).symm x (frame k x) (frame l x)]
      _ = (if e = k then 1 else 0) := by
              simpa [H] using (hinv x e k).1
  have hsum :
      (∑ l : Idx, gInv x e l *
        (2 * (∑ k : Idx, D k * H k l))) =
        2 * (∑ k : Idx, D k *
          (∑ l : Idx, gInv x e l * H k l)) := by
    calc
      (∑ l : Idx, gInv x e l *
        (2 * (∑ k : Idx, D k * H k l)))
          = ∑ l : Idx, ∑ k : Idx,
              gInv x e l * (2 * (D k * H k l)) := by
              refine Finset.sum_congr rfl fun l _ => ?_
              have htwo :
                  2 * (∑ k : Idx, D k * H k l) =
                    ∑ k : Idx, 2 * (D k * H k l) := by
                rw [Finset.mul_sum]
              rw [htwo]
              rw [Finset.mul_sum]
      _ = ∑ k : Idx, ∑ l : Idx,
              gInv x e l * (2 * (D k * H k l)) := by
              rw [Finset.sum_comm]
      _ = ∑ k : Idx, 2 * (D k *
              (∑ l : Idx, gInv x e l * H k l)) := by
              refine Finset.sum_congr rfl fun k _ => ?_
              calc
                (∑ l : Idx, gInv x e l * (2 * (D k * H k l)))
                    = ∑ l : Idx, 2 * (D k * (gInv x e l * H k l)) := by
                        refine Finset.sum_congr rfl fun l _ => ?_
                        ring
                _ = 2 * (∑ l : Idx, D k * (gInv x e l * H k l)) := by
                        rw [Finset.mul_sum]
                _ = 2 * (D k * (∑ l : Idx, gInv x e l * H k l)) := by
                        congr 1
                        rw [Finset.mul_sum]
      _ = 2 * (∑ k : Idx, D k *
              (∑ l : Idx, gInv x e l * H k l)) := by
              rw [Finset.mul_sum]
  calc
    (∑ l : Idx, gInv x e l *
      (metricCovAtBase (I := I) G frame base var x a b l +
        metricCovAtBase (I := I) G frame base var x b a l -
          metricCovAtBase (I := I) G frame base var x l a b))
        =
      ∑ l : Idx, gInv x e l *
        (2 * connDiffLow (I := I) G frame var base var x a b l) := by
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [hcombo l]
    _ = ∑ l : Idx, gInv x e l *
        (2 * (∑ k : Idx, D k * H k l)) := by
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [hconn l]
    _ = 2 * (∑ k : Idx, D k *
        (∑ l : Idx, gInv x e l * H k l)) := hsum
    _ = 2 * (∑ k : Idx, D k * (if e = k then 1 else 0)) := by
          congr 1
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [hcontract k]
    _ = 2 * D e := by
          simp [D]



def componentL2Sq3 (A : Idx -> Idx -> Idx -> Real) : Real :=
  ∑ p : Idx × Idx × Idx, (A p.1 p.2.1 p.2.2) ^ 2

theorem componentL2Sq3_nonneg
    (A : Idx -> Idx -> Idx -> Real) :
    0 <= componentL2Sq3 A := by
  classical
  unfold componentL2Sq3
  exact Finset.sum_nonneg fun p _ => sq_nonneg _



theorem componentL2Sq3_eq_sum
    (A : Idx -> Idx -> Idx -> Real) :
    componentL2Sq3 A =
      ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, (A i j k) ^ 2 := by
  classical
  unfold componentL2Sq3
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fintype.sum_prod_type]



theorem componentL2Sq3_eq_sum_upper_first
    (A : Idx -> Idx -> Idx -> Real) :
    componentL2Sq3 A =
      ∑ k : Idx, ∑ i : Idx, ∑ j : Idx, (A i j k) ^ 2 := by
  classical
  rw [componentL2Sq3_eq_sum]
  calc
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, (A i j k) ^ 2)
        = ∑ i : Idx, ∑ k : Idx, ∑ j : Idx, (A i j k) ^ 2 := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_comm]
    _ = ∑ k : Idx, ∑ i : Idx, ∑ j : Idx, (A i j k) ^ 2 := by
          rw [Finset.sum_comm]



omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem normSq0S_three_eq_componentL2Sq3_of_components [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv :
      Tensor0SBundle.MetricInverseInBasis_gen
        (I := I) g x basis (Tensor0SBundle.identityInvMetric (Idx := Idx)))
    (A : Tensor0SBundle.Tensor0SSpace
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (C : Idx -> Idx -> Idx -> Real)
    (hcomp :
      ∀ d a b : Idx,
        Tensor0SBundle.component0S (I := I) basis A
          (Fin.cons d (fun q : Fin 2 => if q = 0 then a else b)) =
            C d a b) :
    Tensor0SBundle.normSq0S (I := I) g x 3 A =
      componentL2Sq3 C := by
  rw [Tensor0SBundle.normSq0S_three_identity_eq_sum (I := I) g x basis hinv A,
    componentL2Sq3_eq_sum]
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [hcomp d a b]

private theorem three_sq_le (x y z : Real) :
    (x + y - z) ^ 2 <= 3 * (x ^ 2 + y ^ 2 + z ^ 2) := by
  nlinarith [sq_nonneg (x - y), sq_nonneg (x + z), sq_nonneg (y + z)]

private theorem four_sq_le_of_two_eq
    {d x y z : Real} (h : 2 * d = x + y - z) :
    4 * d ^ 2 <= 3 * (x ^ 2 + y ^ 2 + z ^ 2) := by
  calc
    4 * d ^ 2 = (2 * d) ^ 2 := by ring
    _ = (x + y - z) ^ 2 := by rw [h]
    _ <= 3 * (x ^ 2 + y ^ 2 + z ^ 2) := three_sq_le x y z

private def swap12Equiv (α : Type*) : α × α × α ≃ α × α × α where
  toFun p := (p.2.1, p.1, p.2.2)
  invFun p := (p.2.1, p.1, p.2.2)
  left_inv := by
    intro p
    rcases p with ⟨a, b, c⟩
    rfl
  right_inv := by
    intro p
    rcases p with ⟨a, b, c⟩
    rfl

private def cycEquiv (α : Type*) : α × α × α ≃ α × α × α where
  toFun p := (p.2.2, p.1, p.2.1)
  invFun p := (p.2.1, p.2.2, p.1)
  left_inv := by
    intro p
    rcases p with ⟨a, b, c⟩
    rfl
  right_inv := by
    intro p
    rcases p with ⟨a, b, c⟩
    rfl

private def swap23Equiv (α : Type*) : α × α × α ≃ α × α × α where
  toFun p := (p.1, p.2.2, p.2.1)
  invFun p := (p.1, p.2.2, p.2.1)
  left_inv := by
    intro p
    rcases p with ⟨a, b, c⟩
    rfl
  right_inv := by
    intro p
    rcases p with ⟨a, b, c⟩
    rfl

private theorem componentL2Sq3_swap12
    (A : Idx -> Idx -> Idx -> Real) :
    (∑ p : Idx × Idx × Idx, (A p.2.1 p.1 p.2.2) ^ 2) =
      componentL2Sq3 A := by
  classical
  unfold componentL2Sq3
  exact
    Fintype.sum_equiv (swap12Equiv Idx)
      (fun p : Idx × Idx × Idx => (A p.2.1 p.1 p.2.2) ^ 2)
      (fun p : Idx × Idx × Idx => (A p.1 p.2.1 p.2.2) ^ 2)
      (by
        intro p
        rcases p with ⟨a, b, c⟩
        rfl)

private theorem componentL2Sq3_cyc
    (A : Idx -> Idx -> Idx -> Real) :
    (∑ p : Idx × Idx × Idx, (A p.2.2 p.1 p.2.1) ^ 2) =
      componentL2Sq3 A := by
  classical
  unfold componentL2Sq3
  exact
    Fintype.sum_equiv (cycEquiv Idx)
      (fun p : Idx × Idx × Idx => (A p.2.2 p.1 p.2.1) ^ 2)
      (fun p : Idx × Idx × Idx => (A p.1 p.2.1 p.2.2) ^ 2)
      (by
        intro p
        rcases p with ⟨a, b, c⟩
        rfl)

private theorem componentL2Sq3_swap23
    (A : Idx -> Idx -> Idx -> Real) :
    (∑ p : Idx × Idx × Idx, (A p.1 p.2.2 p.2.1) ^ 2) =
      componentL2Sq3 A := by
  classical
  unfold componentL2Sq3
  exact
    Fintype.sum_equiv (swap23Equiv Idx)
      (fun p : Idx × Idx × Idx => (A p.1 p.2.2 p.2.1) ^ 2)
      (fun p : Idx × Idx × Idx => (A p.1 p.2.1 p.2.2) ^ 2)
      (by
        intro p
        rcases p with ⟨a, b, c⟩
        rfl)




theorem gammaSub_l2Sq_le
    (A D : Idx -> Idx -> Idx -> Real)
    (hcombo :
      forall a b e : Idx,
        2 * D a b e = A a b e + A b a e - A e a b) :
    4 * componentL2Sq3 D <= 9 * componentL2Sq3 A := by
  classical
  have hpoint : forall p : Idx × Idx × Idx,
      4 * (D p.1 p.2.1 p.2.2) ^ 2 <=
        3 * ((A p.1 p.2.1 p.2.2) ^ 2 +
          (A p.2.1 p.1 p.2.2) ^ 2 +
          (A p.2.2 p.1 p.2.1) ^ 2) := by
    intro p
    exact four_sq_le_of_two_eq (hcombo p.1 p.2.1 p.2.2)
  have hsum_le :
      (∑ p : Idx × Idx × Idx, 4 * (D p.1 p.2.1 p.2.2) ^ 2) <=
        ∑ p : Idx × Idx × Idx,
          3 * ((A p.1 p.2.1 p.2.2) ^ 2 +
            (A p.2.1 p.1 p.2.2) ^ 2 +
            (A p.2.2 p.1 p.2.1) ^ 2) :=
    Finset.sum_le_sum fun p _ => hpoint p
  calc
    4 * componentL2Sq3 D =
        ∑ p : Idx × Idx × Idx, 4 * (D p.1 p.2.1 p.2.2) ^ 2 := by
          unfold componentL2Sq3
          rw [Finset.mul_sum]
    _ <= ∑ p : Idx × Idx × Idx,
          3 * ((A p.1 p.2.1 p.2.2) ^ 2 +
            (A p.2.1 p.1 p.2.2) ^ 2 +
            (A p.2.2 p.1 p.2.1) ^ 2) := hsum_le
    _ = 3 * (componentL2Sq3 A + componentL2Sq3 A + componentL2Sq3 A) := by
          rw [← Finset.mul_sum]
          congr 1
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
          change componentL2Sq3 A +
              (∑ p : Idx × Idx × Idx, (A p.2.1 p.1 p.2.2) ^ 2) +
              (∑ p : Idx × Idx × Idx, (A p.2.2 p.1 p.2.1) ^ 2) =
            componentL2Sq3 A + componentL2Sq3 A + componentL2Sq3 A
          rw [componentL2Sq3_swap12, componentL2Sq3_cyc]
    _ = 9 * componentL2Sq3 A := by ring


theorem gammaSub_l2_le
    (A D : Idx -> Idx -> Idx -> Real)
    (hcombo :
      forall a b e : Idx,
        2 * D a b e = A a b e + A b a e - A e a b) :
    Real.sqrt (componentL2Sq3 D) <=
      (3 / 2 : Real) * Real.sqrt (componentL2Sq3 A) := by
  have hsq := gammaSub_l2Sq_le (Idx := Idx) A D hcombo
  have hA_nonneg : 0 <= componentL2Sq3 A := componentL2Sq3_nonneg (Idx := Idx) A
  have hD_nonneg : 0 <= componentL2Sq3 D := componentL2Sq3_nonneg (Idx := Idx) D
  have hrhs_nonneg :
      0 <= (3 / 2 : Real) * Real.sqrt (componentL2Sq3 A) :=
    mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  have hsquares :
      (Real.sqrt (componentL2Sq3 D)) ^ 2 <=
        ((3 / 2 : Real) * Real.sqrt (componentL2Sq3 A)) ^ 2 := by
    rw [Real.sq_sqrt hD_nonneg, mul_pow, Real.sq_sqrt hA_nonneg]
    nlinarith
  have habs := (sq_le_sq.mp hsquares)
  simpa [abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg hrhs_nonneg] using habs






theorem gammaEvol_l2Sq_le
    (A D : Idx -> Idx -> Idx -> Real)
    (hcombo :
      forall a b e : Idx,
        D a b e = -A a b e - A b a e + A e a b) :
    componentL2Sq3 D <= 9 * componentL2Sq3 A := by
  classical
  have hpoint : forall p : Idx × Idx × Idx,
      (D p.1 p.2.1 p.2.2) ^ 2 <=
        3 * ((A p.1 p.2.1 p.2.2) ^ 2 +
          (A p.2.1 p.1 p.2.2) ^ 2 +
          (A p.2.2 p.1 p.2.1) ^ 2) := by
    intro p
    calc
      (D p.1 p.2.1 p.2.2) ^ 2 =
          ((-A p.1 p.2.1 p.2.2) +
            (-A p.2.1 p.1 p.2.2) -
              (-A p.2.2 p.1 p.2.1)) ^ 2 := by
            rw [hcombo]
            ring
      _ <= 3 * (((-A p.1 p.2.1 p.2.2) ^ 2) +
          ((-A p.2.1 p.1 p.2.2) ^ 2) +
          ((-A p.2.2 p.1 p.2.1) ^ 2)) :=
            three_sq_le (-A p.1 p.2.1 p.2.2)
              (-A p.2.1 p.1 p.2.2) (-A p.2.2 p.1 p.2.1)
      _ = 3 * ((A p.1 p.2.1 p.2.2) ^ 2 +
          (A p.2.1 p.1 p.2.2) ^ 2 +
          (A p.2.2 p.1 p.2.1) ^ 2) := by ring
  have hsum_le :
      (∑ p : Idx × Idx × Idx, (D p.1 p.2.1 p.2.2) ^ 2) <=
        ∑ p : Idx × Idx × Idx,
          3 * ((A p.1 p.2.1 p.2.2) ^ 2 +
            (A p.2.1 p.1 p.2.2) ^ 2 +
            (A p.2.2 p.1 p.2.1) ^ 2) :=
    Finset.sum_le_sum fun p _ => hpoint p
  calc
    componentL2Sq3 D =
        ∑ p : Idx × Idx × Idx, (D p.1 p.2.1 p.2.2) ^ 2 := rfl
    _ <= ∑ p : Idx × Idx × Idx,
          3 * ((A p.1 p.2.1 p.2.2) ^ 2 +
            (A p.2.1 p.1 p.2.2) ^ 2 +
            (A p.2.2 p.1 p.2.1) ^ 2) := hsum_le
    _ = 3 * (componentL2Sq3 A + componentL2Sq3 A + componentL2Sq3 A) := by
          rw [← Finset.mul_sum]
          congr 1
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
          change componentL2Sq3 A +
              (∑ p : Idx × Idx × Idx, (A p.2.1 p.1 p.2.2) ^ 2) +
              (∑ p : Idx × Idx × Idx, (A p.2.2 p.1 p.2.1) ^ 2) =
            componentL2Sq3 A + componentL2Sq3 A + componentL2Sq3 A
          rw [componentL2Sq3_swap12, componentL2Sq3_cyc]
    _ = 9 * componentL2Sq3 A := by ring



theorem gammaEvol_l2_le
    (A D : Idx -> Idx -> Idx -> Real)
    (hcombo :
      forall a b e : Idx,
        D a b e = -A a b e - A b a e + A e a b) :
    Real.sqrt (componentL2Sq3 D) <=
      3 * Real.sqrt (componentL2Sq3 A) := by
  have hsq := gammaEvol_l2Sq_le (Idx := Idx) A D hcombo
  have hA_nonneg : 0 <= componentL2Sq3 A := componentL2Sq3_nonneg (Idx := Idx) A
  have hD_nonneg : 0 <= componentL2Sq3 D := componentL2Sq3_nonneg (Idx := Idx) D
  have hrhs_nonneg : 0 <= 3 * Real.sqrt (componentL2Sq3 A) :=
    mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  have hsquares :
      (Real.sqrt (componentL2Sq3 D)) ^ 2 <=
        (3 * Real.sqrt (componentL2Sq3 A)) ^ 2 := by
    rw [Real.sq_sqrt hD_nonneg, mul_pow, Real.sq_sqrt hA_nonneg]
    nlinarith
  have habs := (sq_le_sq.mp hsquares)
  simpa [abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg hrhs_nonneg] using habs

private theorem two_sq_le (x y : Real) :
    (x + y) ^ 2 <= 2 * (x ^ 2 + y ^ 2) := by
  nlinarith [sq_nonneg (x - y)]




theorem metricCov_l2Sq_le
    (A D : Idx -> Idx -> Idx -> Real)
    (hcombo :
      forall a b c : Idx,
        A a b c = D a b c + D a c b) :
    componentL2Sq3 A <= 4 * componentL2Sq3 D := by
  classical
  have hpoint : forall p : Idx × Idx × Idx,
      (A p.1 p.2.1 p.2.2) ^ 2 <=
        2 * ((D p.1 p.2.1 p.2.2) ^ 2 +
          (D p.1 p.2.2 p.2.1) ^ 2) := by
    intro p
    calc
      (A p.1 p.2.1 p.2.2) ^ 2 =
          (D p.1 p.2.1 p.2.2 + D p.1 p.2.2 p.2.1) ^ 2 := by
            rw [hcombo]
      _ <= 2 * ((D p.1 p.2.1 p.2.2) ^ 2 +
          (D p.1 p.2.2 p.2.1) ^ 2) :=
            two_sq_le (D p.1 p.2.1 p.2.2) (D p.1 p.2.2 p.2.1)
  have hsum_le :
      (∑ p : Idx × Idx × Idx, (A p.1 p.2.1 p.2.2) ^ 2) <=
        ∑ p : Idx × Idx × Idx,
          2 * ((D p.1 p.2.1 p.2.2) ^ 2 +
            (D p.1 p.2.2 p.2.1) ^ 2) :=
    Finset.sum_le_sum fun p _ => hpoint p
  calc
    componentL2Sq3 A =
        ∑ p : Idx × Idx × Idx, (A p.1 p.2.1 p.2.2) ^ 2 := rfl
    _ <= ∑ p : Idx × Idx × Idx,
          2 * ((D p.1 p.2.1 p.2.2) ^ 2 +
            (D p.1 p.2.2 p.2.1) ^ 2) := hsum_le
    _ = 2 * (componentL2Sq3 D + componentL2Sq3 D) := by
          rw [← Finset.mul_sum]
          congr 1
          rw [Finset.sum_add_distrib]
          change componentL2Sq3 D +
              (∑ p : Idx × Idx × Idx, (D p.1 p.2.2 p.2.1) ^ 2) =
            componentL2Sq3 D + componentL2Sq3 D
          rw [componentL2Sq3_swap23]
    _ = 4 * componentL2Sq3 D := by ring


theorem metricCov_l2_le
    (A D : Idx -> Idx -> Idx -> Real)
    (hcombo :
      forall a b c : Idx,
        A a b c = D a b c + D a c b) :
    Real.sqrt (componentL2Sq3 A) <=
      2 * Real.sqrt (componentL2Sq3 D) := by
  have hsq := metricCov_l2Sq_le (Idx := Idx) A D hcombo
  have hA_nonneg : 0 <= componentL2Sq3 A := componentL2Sq3_nonneg (Idx := Idx) A
  have hD_nonneg : 0 <= componentL2Sq3 D := componentL2Sq3_nonneg (Idx := Idx) D
  have hrhs_nonneg : 0 <= 2 * Real.sqrt (componentL2Sq3 D) :=
    mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  have hsquares :
      (Real.sqrt (componentL2Sq3 A)) ^ 2 <=
        (2 * Real.sqrt (componentL2Sq3 D)) ^ 2 := by
    rw [Real.sq_sqrt hA_nonneg, mul_pow, Real.sq_sqrt hD_nonneg]
    nlinarith
  have habs := (sq_le_sq.mp hsquares)
  simpa [abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg hrhs_nonneg] using habs





omit [SigmaCompactSpace M] [T2Space M] in
theorem covCombo_l2_le [DecidableEq Idx]
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (hLC : ∀ s : Real,
      IsLeviCivita (I := I) (G.connection s) (G.metric s))
    (gInv : DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u)
    (base var : Real)
    (hinv :
      DifferentialGeometry.Integral.Connection.InverseMetricComponentsInFrame
        (I := I) (G.metric var) gInv frame)
    (hinv_id : ∀ e l : Idx, gInv x e l = if e = l then 1 else 0) :
    Real.sqrt
        (componentL2Sq3
          (fun a b e : Idx =>
            DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
                (G.connection var) frame hframe x a b e -
              DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
                (G.connection base) frame hframe x a b e)) <=
      (3 / 2 : Real) *
        Real.sqrt
          (componentL2Sq3
            (fun a b c : Idx =>
              metricCovAtBase (I := I) G frame base var x a b c)) := by
  apply gammaSub_l2_le
  intro a b e
  have h37 :=
    covCombo_gammaSub (I := I) G hLC gInv frame hframe hu hx base var hinv a b e
  have hleft :
      (∑ l : Idx, gInv x e l *
        (metricCovAtBase (I := I) G frame base var x a b l +
          metricCovAtBase (I := I) G frame base var x b a l -
            metricCovAtBase (I := I) G frame base var x l a b)) =
        metricCovAtBase (I := I) G frame base var x a b e +
          metricCovAtBase (I := I) G frame base var x b a e -
            metricCovAtBase (I := I) G frame base var x e a b := by
    simp [hinv_id]
  exact h37.symm.trans hleft



omit [SigmaCompactSpace M] [T2Space M] in
theorem metricCovGeom_l2_le [DecidableEq Idx]
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (hLC : ∀ s : Real,
      IsLeviCivita (I := I) (G.connection s) (G.metric s))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u)
    (base var : Real)
    (hmetric_id : ∀ i j : Idx,
      (G.metric var).inner x (frame i x) (frame j x) =
        if i = j then 1 else 0) :
    Real.sqrt
        (componentL2Sq3
          (fun a b c : Idx =>
            metricCovAtBase (I := I) G frame base var x a b c)) <=
      2 *
        Real.sqrt
          (componentL2Sq3
            (fun a b e : Idx =>
              DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
                  (G.connection var) frame hframe x a b e -
                DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
                  (G.connection base) frame hframe x a b e)) := by
  apply metricCov_l2_le
  intro a b c
  simpa [hmetric_id] using
    metricCov_gammaSub (I := I) G hLC frame hframe hu hx base var a b c




omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem normSqRS_connDiff_eq_componentL2Sq3 [DecidableEq Idx]
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (gInv : DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u)
    (base var : Real)
    (hinv :
      DifferentialGeometry.Integral.Connection.InverseMetricComponentsInFrame
        (I := I) (G.metric var) gInv frame)
    (hinv_id : ∀ e l : Idx, gInv x e l = if e = l then 1 else 0) :
    Tensor0SBundle.normSqRS (I := I) (g := G.metric var) (x := x) 1 2
        (Tensor0SBundle.connectionDifferenceTensorAt
          (I := I) (G.connection var) (G.connection base) x) =
      componentL2Sq3
        (fun a b e : Idx =>
          DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
              (G.connection var) frame hframe x a b e -
            DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
              (G.connection base) frame hframe x a b e) := by
  classical
  have hinvBasis :
      Tensor0SBundle.MetricInverseInBasis_gen
        (I := I) (G.metric var) x (hframe.toBasisAt hx)
        (Tensor0SBundle.identityInvMetric (Idx := Idx)) := by
    intro i j
    constructor
    · simpa [Tensor0SBundle.identityInvMetric, Tensor0SBundle.diagonalInvMetric,
        IsLocalFrameOn.toBasisAt_coe, hinv_id] using (hinv x i j).1
    · simpa [Tensor0SBundle.identityInvMetric, Tensor0SBundle.diagonalInvMetric,
        IsLocalFrameOn.toBasisAt_coe, hinv_id] using (hinv x i j).2
  rw [DifferentialGeometry.Tensor.Coordinates.normSqRS_connectionDifferenceTensorAt_eq_christoffel_sum
    (I := I) (g := G.metric var) (G.connection var) (G.connection base)
    frame hframe hx hinvBasis]
  rw [componentL2Sq3_eq_sum_upper_first]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  exact DifferentialGeometry.Tensor.Coordinates.christoffelSymbolDifferenceInFrame_eq_sub
    (I := I) (G.connection var) (G.connection base) frame hframe i j k
    ((hframe.contMDiffAt hu hx j).mdifferentiableAt one_ne_zero)







omit [SigmaCompactSpace M] [T2Space M] in
theorem covGamma_l2_equiv [DecidableEq Idx]
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (hLC : ∀ s : Real,
      IsLeviCivita (I := I) (G.connection s) (G.metric s))
    (gInv : DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u)
    (base var : Real)
    (hinv :
      DifferentialGeometry.Integral.Connection.InverseMetricComponentsInFrame
        (I := I) (G.metric var) gInv frame)
    (hinv_id : ∀ e l : Idx, gInv x e l = if e = l then 1 else 0)
    (hmetric_id : ∀ i j : Idx,
      (G.metric var).inner x (frame i x) (frame j x) =
        if i = j then 1 else 0) :
    Real.sqrt
        (componentL2Sq3
          (fun a b e : Idx =>
            DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
                (G.connection var) frame hframe x a b e -
              DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
                (G.connection base) frame hframe x a b e)) <=
      (3 / 2 : Real) *
        Real.sqrt
          (componentL2Sq3
            (fun a b c : Idx =>
              metricCovAtBase (I := I) G frame base var x a b c)) ∧
      Real.sqrt
          (componentL2Sq3
            (fun a b c : Idx =>
              metricCovAtBase (I := I) G frame base var x a b c)) <=
        2 *
          Real.sqrt
            (componentL2Sq3
              (fun a b e : Idx =>
                DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
                    (G.connection var) frame hframe x a b e -
                  DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
                    (G.connection base) frame hframe x a b e)) := by
  constructor
  · exact
      covCombo_l2_le (I := I) G hLC gInv frame hframe hu hx base var
        hinv hinv_id
  · exact
      metricCovGeom_l2_le (I := I) G hLC frame hframe hu hx base var
        hmetric_id


def gammaDerivOn
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (base : Real) (u : Set M)
    (gammaDot : M -> Idx -> Idx -> Idx -> Real) : Prop :=
  ∀ x : M, x ∈ u -> ∀ i j k : Idx,
    HasDerivAt
      (fun s : Real =>
        DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
          (G.connection s) frame hframe x i j k)
      (gammaDot x k i j)
      base



omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem varLowDeriv [DecidableEq Idx]
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (base : Real)
    (metricDot : M -> Idx -> Idx -> Real)
    (gammaDot : M -> Idx -> Idx -> Idx -> Real)
    (hmetricVar : metricVarOn (I := I) G frame base u metricDot)
    (hgamma : gammaDerivOn (I := I) G frame hframe base u gammaDot)
    {x : M} (hx : x ∈ u) (i j l : Idx) :
    HasDerivAt
      (fun s : Real => connDiffLow (I := I) G frame s base s x i j l)
      (∑ k : Idx,
        gammaDot x k i j * (G.metric base).inner x (frame k x) (frame l x))
      base := by
  let gammaSub : Idx -> Real -> Real :=
    fun k s =>
      DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
          (G.connection s) frame hframe x i j k -
        DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
          (G.connection base) frame hframe x i j k
  let metricComp : Idx -> Real -> Real :=
    fun k s => (G.metric s).inner x (frame k x) (frame l x)
  have hsum :
      HasDerivAt
        (fun s : Real => ∑ k : Idx, gammaSub k s * metricComp k s)
        (∑ k : Idx,
          gammaDot x k i j * (G.metric base).inner x (frame k x) (frame l x))
        base := by
    simpa [gammaSub, metricComp] using
      (HasDerivAt.fun_sum
        (u := (Finset.univ : Finset Idx))
        (A := fun k s => gammaSub k s * metricComp k s)
        (A' := fun k =>
          gammaDot x k i j * (G.metric base).inner x (frame k x) (frame l x))
        (x := base)
        (fun k _hk => by
          have hγ :
              HasDerivAt (fun s : Real => gammaSub k s)
                (gammaDot x k i j) base := by
            simpa [gammaSub] using
              (hgamma x hx i j k).sub_const
                (DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
                  (G.connection base) frame hframe x i j k)
          have hm :
              HasDerivAt (fun s : Real => metricComp k s)
                (metricDot x k l) base := by
            simpa [metricComp] using hmetricVar x hx k l
          have hmul := hγ.mul hm
          simpa [gammaSub, metricComp] using hmul))
  have hEq :
      (fun s : Real => connDiffLow (I := I) G frame s base s x i j l) =ᶠ[nhds base]
        (fun s : Real => ∑ k : Idx, gammaSub k s * metricComp k s) := by
    exact Filter.Eventually.of_forall fun s => by
      simpa [gammaSub, metricComp] using
        connDiffLow_eq_sum_gammaSub (I := I) G frame hframe hx s base s i j l
  exact hsum.congr_of_eventuallyEq hEq


def gammaVarEqOn
    (gInv : DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (metricCovDerivDt gammaDot : M -> Idx -> Idx -> Idx -> Real)
    (u : Set M) : Prop :=
  ∀ x : M, x ∈ u -> ∀ i j k : Idx,
    gammaDot x k i j =
      metricVarGammaRHS gInv metricCovDerivDt x i j k



omit [TopologicalSpace M] [SigmaCompactSpace M] [T2Space M] in
theorem gammaTraceVar
    (gInv : DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (metricCovDerivDt gammaDot : M -> Idx -> Idx -> Idx -> Real)
    (u : Set M)
    (hgInv_symm : ∀ x : M, x ∈ u -> ∀ i j : Idx,
      gInv x i j = gInv x j i)
    (hmetric_symm : ∀ x : M, x ∈ u -> ∀ d a b : Idx,
      metricCovDerivDt x d a b = metricCovDerivDt x d b a)
    (hgamma : gammaVarEqOn gInv metricCovDerivDt gammaDot u) :
    ∀ x : M, x ∈ u -> ∀ j : Idx,
      (∑ p : Idx, gammaDot x p p j) =
        (1 / 2 : Real) * metricTraceCovAt gInv metricCovDerivDt x j := by
  classical
  intro x hx j
  let A : Real :=
    ∑ p : Idx, ∑ l : Idx,
      gInv x p l * metricCovDerivDt x p j l * (1 / 2 : Real)
  let B : Real :=
    ∑ p : Idx, ∑ l : Idx,
      gInv x p l * metricCovDerivDt x j p l * (1 / 2 : Real)
  let C : Real :=
    ∑ p : Idx, ∑ l : Idx,
      gInv x p l * metricCovDerivDt x l p j * (1 / 2 : Real)
  have hCA : C = A := by
    calc
      C = ∑ l : Idx, ∑ p : Idx,
          gInv x p l * metricCovDerivDt x l p j * (1 / 2 : Real) := by
            change (∑ p : Idx, ∑ l : Idx,
              gInv x p l * metricCovDerivDt x l p j * (1 / 2 : Real)) =
                ∑ l : Idx, ∑ p : Idx,
                  gInv x p l * metricCovDerivDt x l p j * (1 / 2 : Real)
            rw [Finset.sum_comm]
      _ = ∑ l : Idx, ∑ p : Idx,
          gInv x l p * metricCovDerivDt x l j p * (1 / 2 : Real) := by
            refine Finset.sum_congr rfl fun l _ => ?_
            refine Finset.sum_congr rfl fun p _ => ?_
            rw [hgInv_symm x hx p l, hmetric_symm x hx l p j]
      _ = A := by
            rfl
  have hsum :
      (∑ p : Idx, gammaDot x p p j) =
        A + B - C := by
    calc
      (∑ p : Idx, gammaDot x p p j) =
          ∑ p : Idx, metricVarGammaRHS gInv metricCovDerivDt x p j p := by
            refine Finset.sum_congr rfl fun p _ => ?_
            exact hgamma x hx p j p
      _ = A + B - C := by
            unfold A B C metricVarGammaRHS metricVarLowerRHS
            symm
            rw [← Finset.sum_add_distrib]
            rw [← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl fun p _ => ?_
            rw [← Finset.sum_add_distrib]
            rw [← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl fun l _ => ?_
            ring
  calc
    (∑ p : Idx, gammaDot x p p j)
        = A + B - C := hsum
    _ = B := by
        rw [hCA]
        ring
    _ = (1 / 2 : Real) * metricTraceCovAt gInv metricCovDerivDt x j := by
        simp [B, metricTraceCovAt, Finset.mul_sum, mul_comm, mul_assoc]



omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem coeff_invMetric [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M)
    (gInv : DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hinv :
      DifferentialGeometry.Integral.Connection.InverseMetricComponentsInFrame
        (I := I) g gInv frame)
    {x : M} (hx : x ∈ u)
    (k : Idx) (V : TangentSpace I x) :
    hframe.coeff k x V =
      ∑ l : Idx, gInv x k l * g.inner x (frame l x) V := by
  let basis := hframe.toBasisAt hx
  have hcoord :
      basis.coord k V =
        ∑ l : Idx, gInv x k l * g.inner x (basis l) V := by
    symm
    calc
      (∑ l : Idx, gInv x k l * g.inner x (basis l) V)
          = ∑ l : Idx, gInv x k l *
              g.inner x (basis l) (∑ j : Idx, basis.coord j V • basis j) := by
            rw [show (∑ j : Idx, basis.coord j V • basis j) = V from basis.sum_repr V]
      _ = ∑ l : Idx, ∑ j : Idx,
            gInv x k l * (basis.coord j V * g.inner x (basis l) (basis j)) := by
            refine Finset.sum_congr rfl fun l _ => ?_
            rw [map_sum]
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [map_smul]
            simp [smul_eq_mul]
      _ = ∑ j : Idx, basis.coord j V *
            (∑ l : Idx, gInv x k l * g.inner x (basis l) (basis j)) := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun l _ => ?_
            ring
      _ = ∑ j : Idx, basis.coord j V * (if k = j then 1 else 0) := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [show
              (∑ l : Idx, gInv x k l * g.inner x (basis l) (basis j)) =
                (if k = j then 1 else 0) by
                  simpa [basis, IsLocalFrameOn.toBasisAt_coe] using (hinv x k j).1]
      _ = basis.coord k V := by
            simp
  calc
    hframe.coeff k x V = basis.coord k V := by
      simp [basis, IsLocalFrameOn.coeff, hx]
    _ = ∑ l : Idx, gInv x k l * g.inner x (frame l x) V := by
      simpa [basis, IsLocalFrameOn.toBasisAt_coe] using hcoord




def lowerPairDerivOn
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (base : Real) (u : Set M)
    (lowerDot : M -> Idx -> Idx -> Idx -> Real) : Prop :=
  ∀ x : M, x ∈ u -> ∀ i j l : Idx,
    HasDerivAt
      (fun s : Real =>
        (G.metric base).inner x (frame l x)
          ((G.connection s (frame j) x) (frame i x)))
      (lowerDot x i j l)
      base


def gammaFromLower
    (gInv : DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (lowerDot : M -> Idx -> Idx -> Idx -> Real)
    (x : M) (i j k : Idx) : Real :=
  ∑ l : Idx, gInv x k l * lowerDot x i j l



omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem gammaDerivOfLower [DecidableEq Idx]
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (gInv : DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (base : Real)
    (lowerDot : M -> Idx -> Idx -> Idx -> Real)
    (hinv :
      DifferentialGeometry.Integral.Connection.InverseMetricComponentsInFrame
        (I := I) (G.metric base) gInv frame)
    (hlower : lowerPairDerivOn (I := I) G frame base u lowerDot) :
    gammaDerivOn (I := I) G frame hframe base u
      (fun x k i j => gammaFromLower gInv lowerDot x i j k) := by
  intro x hx i j k
  let pair : Idx -> Real -> Real :=
    fun l s =>
      (G.metric base).inner x (frame l x)
        ((G.connection s (frame j) x) (frame i x))
  have hsum :
      HasDerivAt
        (fun s : Real => ∑ l : Idx, gInv x k l * pair l s)
        (∑ l : Idx, gInv x k l * lowerDot x i j l)
        base := by
    simpa [pair] using
      (HasDerivAt.fun_sum
        (u := (Finset.univ : Finset Idx))
        (A := fun l s => gInv x k l * pair l s)
        (A' := fun l => gInv x k l * lowerDot x i j l)
        (x := base)
        (fun l _hl =>
          HasDerivAt.const_mul
            (gInv x k l) (hlower x hx i j l)))
  have hEq :
      (fun s : Real =>
        DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
          (G.connection s) frame hframe x i j k) =ᶠ[nhds base]
        (fun s : Real => ∑ l : Idx, gInv x k l * pair l s) := by
    exact Filter.Eventually.of_forall fun s => by
      simpa [DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame, pair] using
        coeff_invMetric (I := I) (M := M)
          (G.metric base) gInv frame hframe hinv hx k
          ((G.connection s (frame j) x) (frame i x))
  simpa [gammaFromLower, pair] using hsum.congr_of_eventuallyEq hEq



omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem gammaEqOfDeriv
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (gInv : DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (base : Real)
    (metricCovDerivDt gammaDot : M -> Idx -> Idx -> Idx -> Real)
    (hformula :
      gammaDerivOn (I := I) G frame hframe base u
        (fun x k i j =>
          gammaFromLower gInv (metricVarLowerRHS metricCovDerivDt) x i j k))
    (hgamma : gammaDerivOn (I := I) G frame hframe base u gammaDot) :
    gammaVarEqOn gInv metricCovDerivDt gammaDot u := by
  intro x hx i j k
  have huniq := (hformula x hx i j k).unique (hgamma x hx i j k)
  simpa [metricVarGammaRHS, gammaFromLower] using huniq.symm







omit [SigmaCompactSpace M] [T2Space M] in
theorem lcGammaVar [DecidableEq Idx]
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (hLC : ∀ s : Real,
      IsLeviCivita (I := I) (G.connection s) (G.metric s))
    (gInv : DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (_hu : IsOpen u)
    (base : Real)
    (metricDot : M -> Idx -> Idx -> Real)
    (metricCovDerivDt gammaDot : M -> Idx -> Idx -> Idx -> Real)
    (_hinv :
      DifferentialGeometry.Integral.Connection.InverseMetricComponentsInFrame
        (I := I) (G.metric base) gInv frame)
    (hmetricVar :
      metricVarOn (I := I) G frame base u metricDot)
    (_hmetric :
      metricCovVarOn (I := I) G frame base u metricCovDerivDt)
    (_hgamma :
      gammaDerivOn (I := I) G frame hframe base u gammaDot) :
    gammaVarEqOn gInv metricCovDerivDt gammaDot u := by
  intro x hx i j k
  have hlow :
      ∀ l : Idx,
        (∑ a : Idx,
          gammaDot x a i j * (G.metric base).inner x (frame a x) (frame l x)) =
          metricVarLowerRHS metricCovDerivDt x i j l := by
    intro l
    have hL :
        HasDerivAt
          (fun s : Real =>
            2 * connDiffLow (I := I) G frame s base s x i j l)
          (2 * ∑ a : Idx,
            gammaDot x a i j * (G.metric base).inner x (frame a x) (frame l x))
          base := by
      exact HasDerivAt.const_mul (2 : Real)
        (varLowDeriv (I := I) G frame hframe base metricDot gammaDot
          hmetricVar _hgamma hx i j l)
    have hR :
        HasDerivAt
          (fun s : Real =>
            metricCovAtBase (I := I) G frame base s x i j l +
              metricCovAtBase (I := I) G frame base s x j i l -
                metricCovAtBase (I := I) G frame base s x l i j)
          (metricCovDerivDt x i j l +
            metricCovDerivDt x j i l - metricCovDerivDt x l i j)
          base := by
      exact ((_hmetric x hx i j l).add (_hmetric x hx j i l)).sub
        (_hmetric x hx l i j)
    have hEq :
        (fun s : Real =>
            metricCovAtBase (I := I) G frame base s x i j l +
              metricCovAtBase (I := I) G frame base s x j i l -
                metricCovAtBase (I := I) G frame base s x l i j) =ᶠ[nhds base]
          (fun s : Real =>
            2 * connDiffLow (I := I) G frame s base s x i j l) := by
      exact Filter.Eventually.of_forall fun s => by
        exact (finiteDiffKoszul (I := I) G hLC frame hframe _hu hx base s i j l).symm
    have hL_as_R :
        HasDerivAt
          (fun s : Real =>
            metricCovAtBase (I := I) G frame base s x i j l +
              metricCovAtBase (I := I) G frame base s x j i l -
                metricCovAtBase (I := I) G frame base s x l i j)
          (2 * ∑ a : Idx,
            gammaDot x a i j * (G.metric base).inner x (frame a x) (frame l x))
          base := hL.congr_of_eventuallyEq hEq
    have hderiv :
        2 * (∑ a : Idx,
          gammaDot x a i j * (G.metric base).inner x (frame a x) (frame l x)) =
          metricCovDerivDt x i j l +
            metricCovDerivDt x j i l - metricCovDerivDt x l i j :=
      hL_as_R.unique hR
    unfold metricVarLowerRHS
    linarith
  let V : TangentSpace I x :=
    ∑ a : Idx, gammaDot x a i j • frame a x
  have hcoeff :
      hframe.coeff k x V = gammaDot x k i j := by
    let basis := hframe.toBasisAt hx
    have hbasis :
        ∀ a : Idx, basis.repr (frame a x) k = if a = k then 1 else 0 := by
      intro a
      have hframe_eq : frame a x = basis a := by
        simp [basis]
      rw [hframe_eq]
      by_cases h : a = k
      · subst k
        simp
      · simp [h]
    calc
      hframe.coeff k x V = basis.repr V k := by
        simp [basis, IsLocalFrameOn.coeff, hx]
      _ = ∑ a : Idx, gammaDot x a i j * basis.repr (frame a x) k := by
        simp [V, map_sum, map_smul, smul_eq_mul]
      _ = ∑ a : Idx, gammaDot x a i j * (if a = k then 1 else 0) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [hbasis a]
      _ = gammaDot x k i j := by
        simp
  have hinner :
      ∀ l : Idx,
        (G.metric base).inner x (frame l x) V =
          metricVarLowerRHS metricCovDerivDt x i j l := by
    intro l
    calc
      (G.metric base).inner x (frame l x) V =
          ∑ a : Idx,
            gammaDot x a i j * (G.metric base).inner x (frame l x) (frame a x) := by
            simp [V, map_sum, smul_eq_mul]
      _ = ∑ a : Idx,
            gammaDot x a i j * (G.metric base).inner x (frame a x) (frame l x) := by
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [(G.metric base).symm x (frame l x) (frame a x)]
      _ = metricVarLowerRHS metricCovDerivDt x i j l := hlow l
  calc
    gammaDot x k i j = hframe.coeff k x V := hcoeff.symm
    _ = ∑ l : Idx, gInv x k l * (G.metric base).inner x (frame l x) V := by
      exact coeff_invMetric (I := I) (M := M)
        (G.metric base) gInv frame hframe _hinv hx k V
    _ = ∑ l : Idx, gInv x k l * metricVarLowerRHS metricCovDerivDt x i j l := by
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [hinner l]
    _ = metricVarGammaRHS gInv metricCovDerivDt x i j k := by
      rfl


omit [SigmaCompactSpace M] [T2Space M] in
theorem gammaTraceVar_of_lcGammaVar [DecidableEq Idx]
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    (hLC : ∀ s : Real,
      IsLeviCivita (I := I) (G.connection s) (G.metric s))
    (gInv : DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u)
    (base : Real)
    (metricDot : M -> Idx -> Idx -> Real)
    (metricCovDerivDt gammaDot : M -> Idx -> Idx -> Idx -> Real)
    (hinv :
      DifferentialGeometry.Integral.Connection.InverseMetricComponentsInFrame
        (I := I) (G.metric base) gInv frame)
    (hmetricVar :
      metricVarOn (I := I) G frame base u metricDot)
    (hmetric :
      metricCovVarOn (I := I) G frame base u metricCovDerivDt)
    (hgamma :
      gammaDerivOn (I := I) G frame hframe base u gammaDot) :
    ∀ x : M, x ∈ u -> ∀ j : Idx,
      (∑ p : Idx, gammaDot x p p j) =
        (1 / 2 : Real) * metricTraceCovAt gInv metricCovDerivDt x j := by
  have hgammaEq :
      gammaVarEqOn gInv metricCovDerivDt gammaDot u :=
    lcGammaVar (I := I) G hLC gInv frame hframe hu base metricDot
      metricCovDerivDt gammaDot hinv hmetricVar hmetric hgamma
  have hgInv_symm :
      ∀ x : M, x ∈ u -> ∀ i j : Idx, gInv x i j = gInv x j i := by
    intro x _ i j
    exact DifferentialGeometry.Integral.Connection.invComp_symm (I := I) (g := G.metric base)
      (gInv := gInv) frame hinv x i j
  have hmetric_symm :
      ∀ x : M, x ∈ u -> ∀ d a b : Idx,
        metricCovDerivDt x d a b = metricCovDerivDt x d b a :=
    metricCovVar_symm (I := I) G frame base u metricCovDerivDt hmetric
  exact gammaTraceVar gInv metricCovDerivDt gammaDot u
    hgInv_symm hmetric_symm hgammaEq




end DifferentialGeometry.Integral.Connection
