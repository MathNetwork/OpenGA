import DifferentialGeometry.Geometry.Operator.LaplacianMinimum
import DifferentialGeometry.Geometry.Operator.GradientRegularity
import DifferentialGeometry.Geometry.Curvature.Realized.MetricFamily

set_option autoImplicit false
set_option linter.style.longLine false









namespace DifferentialGeometry.Integral.Connection

noncomputable section

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {Time : Type*}

private instance tangentSpace_finiteDimensional (x : M) :
    FiniteDimensional Real (TangentSpace I x) :=
  inferInstanceAs (FiniteDimensional Real E)



def gradientAt
    (G : RealizedMetricFamily (I := I) (M := M) Time)
    (t : Time) (f : M -> Real) (x : M) : TangentSpace I x :=
  gradientFun (I := I) (G.metric t) f x


def divergenceAt
    (G : RealizedMetricFamily (I := I) (M := M) Time)
    (t : Time) (X : (x : M) -> TangentSpace I x) (x : M) : Real :=
  divergence (I := I) (G.connection t) X x


def laplacianAt
    (G : RealizedMetricFamily (I := I) (M := M) Time)
    (t : Time) (f : M -> Real) (x : M) : Real :=
  laplacian (I := I) (G.connection t) (G.metric t) f x


def driftTerm
    (G : RealizedMetricFamily (I := I) (M := M) Time)
    (t : Time) (X : (x : M) -> TangentSpace I x)
    (f : M -> Real) (x : M) : Real :=
  (G.metric t).inner x (X x) (gradientAt (I := I) G t f x)


def heatOperatorWithDrift
    (G : RealizedMetricFamily (I := I) (M := M) Time)
    (t : Time) (X : (x : M) -> TangentSpace I x)
    (f : M -> Real) (x : M) : Real :=
  laplacianAt (I := I) G t f x + driftTerm (I := I) G t X f x


def heatOperator
    (G : RealizedMetricFamily (I := I) (M := M) Time)
    (t : Time) (f : M -> Real) (x : M) : Real :=
  laplacianAt (I := I) G t f x

@[simp] theorem driftTerm_zero_drift
    (G : RealizedMetricFamily (I := I) (M := M) Time)
    (t : Time) (f : M -> Real) (x : M) :
    driftTerm (I := I) G t (fun y : M => (0 : TangentSpace I y)) f x = 0 := by
  simp [driftTerm]

@[simp] theorem heatOperator_eq_laplacianAt
    (G : RealizedMetricFamily (I := I) (M := M) Time)
    (t : Time) (f : M -> Real) (x : M) :
    heatOperator (I := I) G t f x = laplacianAt (I := I) G t f x := by
  rfl

theorem heatOperatorWithDrift_zero_drift
    (G : RealizedMetricFamily (I := I) (M := M) Time)
    (t : Time) (f : M -> Real) (x : M) :
    heatOperatorWithDrift (I := I) G t
        (fun y : M => (0 : TangentSpace I y)) f x =
      heatOperator (I := I) G t f x := by
  simp [heatOperatorWithDrift, heatOperator]

section FamilyAlgebraicRules

variable [VectorBundle Real E (TangentSpace I : M -> Type _)]


omit [VectorBundle ℝ E (TangentSpace I : M → Type _)] in
theorem driftTerm_sub_const
    (G : RealizedMetricFamily (I := I) (M := M) Time)
    (t : Time) (X : (x : M) -> TangentSpace I x)
    {f : M -> Real} (c : Real) {x : M}
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x) :
    driftTerm (I := I) G t X (fun y : M => f y - c) x =
      driftTerm (I := I) G t X f x := by
  unfold driftTerm gradientAt
  rw [gradientFun_sub (I := I) (G.metric t) hf mdifferentiableAt_const]
  rw [gradientFun_const]
  simp


omit [VectorBundle ℝ E (TangentSpace I : M → Type _)] in
theorem driftTerm_const_smul
    (G : RealizedMetricFamily (I := I) (M := M) Time)
    (t : Time) (X : (x : M) -> TangentSpace I x)
    (a : Real) {f : M -> Real} {x : M}
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x) :
    driftTerm (I := I) G t X (a • f) x =
      a * driftTerm (I := I) G t X f x := by
  unfold driftTerm gradientAt
  rw [gradientFun_const_smul (I := I) (G.metric t) a hf]
  simp


omit [VectorBundle ℝ E (TangentSpace I : M → Type _)] in
theorem heatOperatorWithDrift_sub_const
    (G : RealizedMetricFamily (I := I) (M := M) Time)
    (t : Time) (X : (x : M) -> TangentSpace I x)
    {f : M -> Real} (c : Real)
    (hf : forall y : M, MDifferentiableAt I 𝓘(Real, Real) f y)
    (x : M) :
    heatOperatorWithDrift (I := I) G t X (fun y : M => f y - c) x =
      heatOperatorWithDrift (I := I) G t X f x := by
  unfold heatOperatorWithDrift laplacianAt
  rw [laplacian_sub_const (I := I) (G.connection t) (G.metric t) c hf x]
  rw [driftTerm_sub_const (I := I) G t X c (hf x)]


theorem heatOperatorWithDrift_const_smul
    (G : RealizedMetricFamily (I := I) (M := M) Time)
    (t : Time) (X : (x : M) -> TangentSpace I x)
    (a : Real) {f : M -> Real} {x : M}
    (hf : forall y : M, MDifferentiableAt I 𝓘(Real, Real) f y)
    (hgrad : MDiffAt (T% fun y : M =>
      gradientFun (I := I) (G.metric t) f y) x) :
    heatOperatorWithDrift (I := I) G t X (a • f) x =
      a * heatOperatorWithDrift (I := I) G t X f x := by
  unfold heatOperatorWithDrift laplacianAt
  rw [laplacian_const_smul (I := I) (G.connection t) (G.metric t) a hf hgrad]
  rw [driftTerm_const_smul (I := I) G t X a (hf x)]
  ring


theorem laplacianAt_sub
    (G : RealizedMetricFamily (I := I) (M := M) Time)
    (t : Time) {f h : M -> Real} {x : M}
    (hf : forall y : M, MDifferentiableAt I 𝓘(Real, Real) f y)
    (hh : forall y : M, MDifferentiableAt I 𝓘(Real, Real) h y)
    (hgradf : MDiffAt (T% fun y : M =>
      gradientFun (I := I) (G.metric t) f y) x)
    (hgradh : MDiffAt (T% fun y : M =>
      gradientFun (I := I) (G.metric t) h y) x) :
    laplacianAt (I := I) G t (fun y : M => f y - h y) x =
      laplacianAt (I := I) G t f x -
        laplacianAt (I := I) G t h x := by
  unfold laplacianAt
  exact laplacian_sub (I := I) (G.connection t) (G.metric t)
    hf hh hgradf hgradh


theorem laplacianAt_smul
    (G : RealizedMetricFamily (I := I) (M := M) Time)
    (t : Time) (a : Real) {f : M -> Real} {x : M}
    (hf : forall y : M, MDifferentiableAt I 𝓘(Real, Real) f y)
    (hgrad : MDiffAt (T% fun y : M =>
      gradientFun (I := I) (G.metric t) f y) x) :
    laplacianAt (I := I) G t (a • f) x =
      a * laplacianAt (I := I) G t f x := by
  unfold laplacianAt
  exact laplacian_const_smul (I := I) (G.connection t) (G.metric t)
    a hf hgrad


omit [VectorBundle ℝ E (TangentSpace I : M → Type _)] in
theorem gradientAt_mul
    (G : RealizedMetricFamily (I := I) (M := M) Time)
    (t : Time) {f h : M -> Real} {x : M}
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hh : MDifferentiableAt I 𝓘(Real, Real) h x) :
    gradientAt (I := I) G t (fun y : M => f y * h y) x =
      f x • gradientAt (I := I) G t h x +
        h x • gradientAt (I := I) G t f x := by
  unfold gradientAt
  exact gradientFun_mul (I := I) (G.metric t) hf hh


omit [VectorBundle ℝ E (TangentSpace I : M → Type _)] in
theorem gradientAt_rpow
    (G : RealizedMetricFamily (I := I) (M := M) Time)
    (t : Time) {f : M -> Real} {x : M} (p : Real)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hpos : 0 < f x) :
    gradientAt (I := I) G t (fun y : M => f y ^ p) x =
      (p * f x ^ (p - 1)) • gradientAt (I := I) G t f x := by
  unfold gradientAt
  exact gradientFun_rpow (I := I) (G.metric t) p hf hpos


theorem laplacianAt_mul
    (G : RealizedMetricFamily (I := I) (M := M) Time)
    (t : Time) {f h : M -> Real} {x : M}
    (hf : forall y : M, MDifferentiableAt I 𝓘(Real, Real) f y)
    (hh : forall y : M, MDifferentiableAt I 𝓘(Real, Real) h y)
    (hgradf : MDiffAt (T% fun y : M =>
      gradientFun (I := I) (G.metric t) f y) x)
    (hgradh : MDiffAt (T% fun y : M =>
      gradientFun (I := I) (G.metric t) h y) x)
    (hfgradh : MDiffAt (T% (f • fun y : M =>
      gradientFun (I := I) (G.metric t) h y)) x)
    (hhgradf : MDiffAt (T% (h • fun y : M =>
      gradientFun (I := I) (G.metric t) f y)) x) :
    laplacianAt (I := I) G t (fun y : M => f y * h y) x =
      f x * laplacianAt (I := I) G t h x +
        h x * laplacianAt (I := I) G t f x +
          2 * (G.metric t).inner x
            (gradientAt (I := I) G t f x)
            (gradientAt (I := I) G t h x) := by
  unfold laplacianAt gradientAt
  exact laplacian_mul (I := I) (G.connection t) (G.metric t)
    hf hh hgradf hgradh hfgradh hhgradf



theorem laplacianAt_mul_of_scalarRegular
    (G : RealizedMetricFamily (I := I) (M := M) Time)
    (t : Time) {f h : M -> Real} {x : M}
    (hf : forall y : M, MDifferentiableAt I 𝓘(Real, Real) f y)
    (hh : forall y : M, MDifferentiableAt I 𝓘(Real, Real) h y)
    (hgradf : forall y : M, MDiffAt (T% fun z : M =>
      gradientFun (I := I) (G.metric t) f z) y)
    (hgradh : forall y : M, MDiffAt (T% fun z : M =>
      gradientFun (I := I) (G.metric t) h z) y) :
    laplacianAt (I := I) G t (fun y : M => f y * h y) x =
      f x * laplacianAt (I := I) G t h x +
        h x * laplacianAt (I := I) G t f x +
          2 * (G.metric t).inner x
            (gradientAt (I := I) G t f x)
            (gradientAt (I := I) G t h x) := by
  exact laplacianAt_mul (I := I) G t
    hf hh (hgradf x) (hgradh x)
    ((hf x).smul_section (hgradh x))
    ((hh x).smul_section (hgradf x))


theorem laplacianAt_rpow
    (G : RealizedMetricFamily (I := I) (M := M) Time)
    (t : Time) {f : M -> Real} {x : M} (p : Real)
    (hf : forall y : M, MDifferentiableAt I 𝓘(Real, Real) f y)
    (hpos : forall y : M, 0 < f y)
    (hgrad : MDiffAt (T% fun y : M =>
      gradientFun (I := I) (G.metric t) f y) x) :
    laplacianAt (I := I) G t (fun y : M => f y ^ p) x =
      (p * f x ^ (p - 1)) * laplacianAt (I := I) G t f x +
        (p * (p - 1) * f x ^ (p - 2)) *
          (G.metric t).inner x
            (gradientAt (I := I) G t f x)
            (gradientAt (I := I) G t f x) := by
  unfold laplacianAt gradientAt
  exact laplacian_rpow (I := I) (G.connection t) (G.metric t)
    p hf hpos hgrad


theorem laplacianAt_sq
    (G : RealizedMetricFamily (I := I) (M := M) Time)
    (t : Time) {f : M -> Real} {x : M}
    (hf_all : forall y : M, MDifferentiableAt I 𝓘(Real, Real) f y)
    (hf_x : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hgrad : MDiffAt (T% fun y : M =>
      gradientFun (I := I) (G.metric t) f y) x)
    (hfg : MDiffAt (T% (f • fun y : M =>
      gradientFun (I := I) (G.metric t) f y)) x) :
    laplacianAt (I := I) G t (fun y : M => f y ^ 2) x =
      2 * f x * laplacianAt (I := I) G t f x +
        2 * (G.metric t).inner x
          (gradientAt (I := I) G t f x)
          (gradientAt (I := I) G t f x) := by
  have hhalf :=
    half_laplacian_mul_self
      (I := I) (G.connection t) (G.metric t) (f := f) (x := x)
      hf_all hf_x hgrad hfg
  unfold laplacianAt gradientAt
  have hpow :
      (fun y : M => f y ^ 2) = fun y : M => f y * f y := by
    funext y
    ring
  rw [hpow]
  have hmain :
      laplacian (I := I) (G.connection t) (G.metric t)
          (fun y : M => f y * f y) x =
        2 * (f x * laplacian (I := I) (G.connection t) (G.metric t) f x +
          (G.metric t).inner x
            (gradientFun (I := I) (G.metric t) f x)
            (gradientFun (I := I) (G.metric t) f x)) := by
    linarith
  rw [hmain]
  ring



theorem laplacianAt_sq_of_scalarRegular
    (G : RealizedMetricFamily (I := I) (M := M) Time)
    (t : Time) {f : M -> Real} {x : M}
    (hf : ∀ y : M, MDifferentiableAt I 𝓘(Real, Real) f y)
    (hgrad : ∀ y : M, MDiffAt (T% fun z : M =>
      gradientFun (I := I) (G.metric t) f z) y) :
    laplacianAt (I := I) G t (fun y : M => f y ^ 2) x =
      2 * f x * laplacianAt (I := I) G t f x +
        2 * (G.metric t).inner x
          (gradientAt (I := I) G t f x)
          (gradientAt (I := I) G t f x) := by
  exact laplacianAt_sq (I := I) G t
    hf (hf x) (hgrad x)
    (scalar_mul_grad_mdiffAt (I := I) (G.metric t) hf hgrad)

end FamilyAlgebraicRules

@[simp] theorem gradientAt_eq
    (G : RealizedMetricFamily (I := I) (M := M) Time)
    (t : Time) (f : M -> Real) (x : M) :
    gradientAt (I := I) G t f x = gradientFun (I := I) (G.metric t) f x := by
  rfl

omit [FiniteDimensional ℝ E] in
@[simp] theorem divergenceAt_eq
    (G : RealizedMetricFamily (I := I) (M := M) Time)
    (t : Time) (X : (x : M) -> TangentSpace I x) (x : M) :
    divergenceAt (I := I) G t X x =
      divergence (I := I) (G.connection t) X x := by
  rfl

@[simp] theorem laplacianAt_eq
    (G : RealizedMetricFamily (I := I) (M := M) Time)
    (t : Time) (f : M -> Real) (x : M) :
    laplacianAt (I := I) G t f x =
      laplacian (I := I) (G.connection t) (G.metric t) f x := by
  rfl




theorem driftTerm_eq_zero_at_spatial_min
    [I.Boundaryless]
    (G : RealizedMetricFamily (I := I) (M := M) Time)
    (t : Time) (X : (x : M) -> TangentSpace I x)
    {f : M -> Real} {x : M}
    (hmin : IsLocalMin f x)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x) :
    driftTerm (I := I) G t X f x = 0 := by
  unfold driftTerm gradientAt
  rw [gradientFun_eq_zero_at_spatial_min (I := I) (G.metric t) hmin hf]
  simp


def LaplacianNonnegativeAtSpatialMinFamily
    [I.Boundaryless]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : RealizedMetricFamily (I := I) (M := M) Time) : Prop :=
  forall t : Time,
    LaplacianNonnegativeAtSpatialMin (I := I) (G.connection t) (G.metric t)



theorem laplacianNonnegativeAtSpatialMinFamily_of_realizedMetricFamily
    [I.Boundaryless]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    (G : RealizedMetricFamily (I := I) (M := M) Time) :
    LaplacianNonnegativeAtSpatialMinFamily (I := I) G := by
  intro t
  exact laplacianNonnegativeAtSpatialMin_of_metricCompatible (I := I)
    (G.connection t) (G.metric t) (G.metricCompatible t)


theorem heatOperatorWithDrift_at_spatial_min_nonneg
    [I.Boundaryless]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    (G : RealizedMetricFamily (I := I) (M := M) Time)
    (t : Time) (X : (x : M) -> TangentSpace I x)
    {f : M -> Real} {x : M}
    (hmin : IsLocalMin f x)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hf_near : ∀ᶠ y in nhds x, MDifferentiableAt I 𝓘(Real, Real) f y)
    (hgrad : MDiffAt (T% fun y : M => gradientFun (I := I) (G.metric t) f y) x) :
    0 <= heatOperatorWithDrift (I := I) G t X f x := by
  unfold heatOperatorWithDrift
  rw [driftTerm_eq_zero_at_spatial_min (I := I) G t X hmin hf, add_zero]
  exact laplacian_nonneg_at_spatial_min_of_metricCompatible (I := I)
    (G.connection t) (G.metric t) (G.metricCompatible t) hmin hf hf_near hgrad

end

end DifferentialGeometry.Integral.Connection
