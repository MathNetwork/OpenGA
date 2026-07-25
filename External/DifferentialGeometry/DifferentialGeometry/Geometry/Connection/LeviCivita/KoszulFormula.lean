import DifferentialGeometry.Geometry.Connection.LeviCivita.Basic
import DifferentialGeometry.Geometry.Curvature.Realized.Operators
import DifferentialGeometry.Tensor.RSTensor.Derivation.NablaOnTensors
import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorField.LieBracket
import Mathlib.Geometry.Manifold.VectorBundle.Tensoriality
import DifferentialGeometry.Geometry.Connection.LeviCivita.Koszul

set_option autoImplicit false
set_option linter.style.longLine false



















namespace DifferentialGeometry.Integral.Connection

noncomputable section

open Bundle
open DifferentialGeometry.Integral.Connection
open scoped Bundle Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M]

private instance tangentSpace_finiteDimensional (x : M) :
    FiniteDimensional Real (TangentSpace I x) :=
  inferInstanceAs (FiniteDimensional Real E)









def tangentConstAt (x : M) (v : TangentSpace I x) (p : M) :
    TangentSpace I p :=
  TensorLieDeriv.tangentConstInChart (𝕜 := Real) (I := I) x v p

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
@[simp] theorem tangentConstAt_apply (x : M) (v : TangentSpace I x) (p : M) :
    tangentConstAt (I := I) x v p =
      TensorLieDeriv.tangentConstInChart (𝕜 := Real) (I := I) x v p := by
  rfl

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
@[simp] theorem tangentConstAt_self (x : M) (v : TangentSpace I x) :
    tangentConstAt (I := I) x v x = v := by
  unfold tangentConstAt
  rw [TensorLieDeriv.tangentConstInChart_apply]
  have hL :
      (trivializationAt E (TangentSpace I) x).symmL Real x =
        (1 : E →L[Real] E) := by
    rw [TangentBundle.symmL_trivializationAt_eq_core
      (𝕜 := Real) (I := I) (b₀ := x) (b := x) (mem_chart_source H x)]
    ext w
    exact (tangentBundleCore I M).coordChange_self (achart H x) x
      (by rw [tangentBundleCore_baseSet, coe_achart]; exact mem_chart_source H x) w
  rw [hL]
  rfl

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
@[simp] theorem tangentConstAt_add (x : M) (v w : TangentSpace I x) :
    (tangentConstAt (I := I) x (v + w) : (p : M) -> TangentSpace I p) =
      (tangentConstAt (I := I) x v : (p : M) -> TangentSpace I p) +
        tangentConstAt (I := I) x w := by
  unfold tangentConstAt
  exact TensorLieDeriv.tangentConstInChart_add (𝕜 := Real) (I := I) x v w

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
@[simp] theorem tangentConstAt_smul (x : M) (a : Real) (v : TangentSpace I x) :
    (tangentConstAt (I := I) x (a • v) : (p : M) -> TangentSpace I p) =
      a • (tangentConstAt (I := I) x v : (p : M) -> TangentSpace I p) := by
  unfold tangentConstAt
  exact TensorLieDeriv.tangentConstInChart_smul (𝕜 := Real) (I := I) x a v

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem mdifferentiableAt_tangentConstAt_self
    (x : M) (v : TangentSpace I x) :
    MDiffAt (T% (tangentConstAt (I := I) x v : (p : M) -> TangentSpace I p)) x := by
  unfold tangentConstAt
  exact TensorLieDeriv.mdifferentiableAt_tangentConstInChart_of_mem
    (𝕜 := Real) (I := I) (x₀ := x) (p := x) v
    (mem_baseSet_trivializationAt E (TangentSpace I) x)



omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem mdifferentiableAt_metric_inner
    (g : SmoothRiemannianMetric I M)
    {X Y : (p : M) -> TangentSpace I p} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    MDiffAt (fun y : M => g.inner y (X y) (Y y)) x := by
  have hg :
      MDifferentiableAt I
        (I.prod 𝓘(Real, E →L[Real] E →L[Real] Real))
        (fun y : M =>
          TotalSpace.mk' (E →L[Real] E →L[Real] Real)
            (E := fun y : M =>
              TangentSpace I y →L[Real] TangentSpace I y →L[Real] Real)
            y (g.inner y)) x :=
    g.contMDiff.mdifferentiableAt (by simp)
  have htotal :
      MDifferentiableAt I (I.prod 𝓘(Real, Real))
        (fun y : M =>
          TotalSpace.mk' Real (E := Bundle.Trivial M Real) y
            (g.inner y (X y) (Y y))) x := by
    exact MDifferentiableAt.clm_bundle_apply₂
      (F₁ := E) (F₂ := E) hg hX hY
  rw [mdifferentiableAt_totalSpace] at htotal
  exact htotal.2


def directionalDerivAlong
    (X : (p : M) -> TangentSpace I p) (f : M -> Real) (x : M) : Real :=
  extDerivFun (I := I) f x (X x)

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] in
@[simp] theorem directionalDerivAlong_add_left
    (X X' : (p : M) -> TangentSpace I p) (f : M -> Real) (x : M) :
  directionalDerivAlong (I := I) (X + X') f x =
      directionalDerivAlong (I := I) X f x +
        directionalDerivAlong (I := I) X' f x := by
  unfold directionalDerivAlong
  rw [Pi.add_apply, map_add]

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] in
@[simp] theorem directionalDerivAlong_smul_left
    (a : Real) (X : (p : M) -> TangentSpace I p) (f : M -> Real) (x : M) :
  directionalDerivAlong (I := I) (a • X) f x =
      a * directionalDerivAlong (I := I) X f x := by
  unfold directionalDerivAlong
  rw [Pi.smul_apply, map_smul]
  rfl

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] in
private theorem directionalDerivAlong_add_fun
    (X : (p : M) -> TangentSpace I p) {f h : M -> Real} (x : M)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hh : MDifferentiableAt I 𝓘(Real, Real) h x) :
    directionalDerivAlong (I := I) X (f + h) x =
      directionalDerivAlong (I := I) X f x +
        directionalDerivAlong (I := I) X h x := by
  unfold directionalDerivAlong
  rw [extDerivFun_add hf hh]
  rw [ContinuousLinearMap.add_apply]






def koszulScalar
    (g : SmoothRiemannianMetric I M)
    (X Y Z : (p : M) -> TangentSpace I p) (x : M) : Real :=
  directionalDerivAlong (I := I) X (fun y : M => g.inner y (Y y) (Z y)) x +
    directionalDerivAlong (I := I) Y (fun y : M => g.inner y (Z y) (X y)) x -
    directionalDerivAlong (I := I) Z (fun y : M => g.inner y (X y) (Y y)) x -
    g.inner x (X x) (VectorField.mlieBracket I Y Z x) +
    g.inner x (Y x) (VectorField.mlieBracket I Z X x) +
    g.inner x (Z x) (VectorField.mlieBracket I X Y x)

omit [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M] in
private theorem koszulScalar_add_first
    (g : SmoothRiemannianMetric I M)
    (X X' Y Z : (p : M) -> TangentSpace I p) (x : M)
    (hX : MDiffAt (T% X) x) (hX' : MDiffAt (T% X') x)
    (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    koszulScalar (I := I) g (X + X') Y Z x =
      koszulScalar (I := I) g X Y Z x +
        koszulScalar (I := I) g X' Y Z x := by
  have hZX := mdifferentiableAt_metric_inner (I := I) g hZ hX
  have hZX' := mdifferentiableAt_metric_inner (I := I) g hZ hX'
  have hXY := mdifferentiableAt_metric_inner (I := I) g hX hY
  have hX'Y := mdifferentiableAt_metric_inner (I := I) g hX' hY
  unfold koszulScalar directionalDerivAlong
  rw [show (fun y : M => g.inner y (Z y) ((X + X') y)) =
      (fun y : M => g.inner y (Z y) (X y)) +
        (fun y : M => g.inner y (Z y) (X' y)) by
        funext y; simp [Pi.add_apply]]
  rw [extDerivFun_add hZX hZX']
  rw [show (fun y : M => g.inner y ((X + X') y) (Y y)) =
      (fun y : M => g.inner y (X y) (Y y)) +
        (fun y : M => g.inner y (X' y) (Y y)) by
        funext y; simp [Pi.add_apply]]
  rw [extDerivFun_add hXY hX'Y]
  rw [VectorField.mlieBracket_add_right (I := I) (V := Z) hX hX']
  rw [VectorField.mlieBracket_add_left (I := I) (W := Y) hX hX']
  simp [Pi.add_apply, map_add, ContinuousLinearMap.add_apply]
  abel_nf

omit [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M] in
private theorem koszulScalar_add_second
    (g : SmoothRiemannianMetric I M)
    (X Y Y' Z : (p : M) -> TangentSpace I p) (x : M)
    (hX : MDiffAt (T% X) x)
    (hY : MDiffAt (T% Y) x) (hY' : MDiffAt (T% Y') x)
    (hZ : MDiffAt (T% Z) x) :
    koszulScalar (I := I) g X (Y + Y') Z x =
      koszulScalar (I := I) g X Y Z x +
        koszulScalar (I := I) g X Y' Z x := by
  have hYZ := mdifferentiableAt_metric_inner (I := I) g hY hZ
  have hY'Z := mdifferentiableAt_metric_inner (I := I) g hY' hZ
  have hXY := mdifferentiableAt_metric_inner (I := I) g hX hY
  have hXY' := mdifferentiableAt_metric_inner (I := I) g hX hY'
  unfold koszulScalar
  rw [show (fun y : M => g.inner y ((Y + Y') y) (Z y)) =
      (fun y : M => g.inner y (Y y) (Z y)) +
        (fun y : M => g.inner y (Y' y) (Z y)) by
        funext y; simp [Pi.add_apply]]
  rw [directionalDerivAlong_add_fun (I := I) X x hYZ hY'Z]
  rw [directionalDerivAlong_add_left]
  rw [show (fun y : M => g.inner y (X y) ((Y + Y') y)) =
      (fun y : M => g.inner y (X y) (Y y)) +
        (fun y : M => g.inner y (X y) (Y' y)) by
        funext y; simp [Pi.add_apply]]
  rw [directionalDerivAlong_add_fun (I := I) Z x hXY hXY']
  rw [VectorField.mlieBracket_add_left (I := I) (W := Z) hY hY']
  rw [VectorField.mlieBracket_add_right (I := I) (V := X) hY hY']
  simp [Pi.add_apply, map_add, ContinuousLinearMap.add_apply]
  abel_nf

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] in
private theorem extDerivFun_mul_at
    {f h : M -> Real} {x : M} (v : TangentSpace I x)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hh : MDifferentiableAt I 𝓘(Real, Real) h x) :
    extDerivFun (I := I) (fun y : M => f y * h y) x v =
      f x * extDerivFun (I := I) h x v +
        extDerivFun (I := I) f x v * h x := by
  change extDerivFun (I := I) (f • h) x v =
      f x * extDerivFun (I := I) h x v +
        extDerivFun (I := I) f x v * h x
  have hprod := fromTangentSpace_mfderiv_smul_apply
    (I := I) (f := f) (g := h) hf hh v
  simpa [extDerivFun, Pi.smul_apply, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
    using hprod

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] in
private theorem directionalDerivAlong_mul_fun
    (X : (p : M) -> TangentSpace I p) {f h : M -> Real} (x : M)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hh : MDifferentiableAt I 𝓘(Real, Real) h x) :
    directionalDerivAlong (I := I) X (fun y : M => f y * h y) x =
      f x * directionalDerivAlong (I := I) X h x +
        directionalDerivAlong (I := I) X f x * h x := by
  unfold directionalDerivAlong
  exact extDerivFun_mul_at (I := I) (v := X x) hf hh

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] in
private theorem directionalDerivAlong_smul_fun_left
    {f : M -> Real} (X : (p : M) -> TangentSpace I p) (h : M -> Real) (x : M) :
    directionalDerivAlong (I := I) (f • X) h x =
      f x * directionalDerivAlong (I := I) X h x := by
  unfold directionalDerivAlong
  change (extDerivFun (I := I) h x) (f x • X x) =
    f x * (extDerivFun (I := I) h x) (X x)
  rw [map_smul]
  rfl

omit [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M] in
private theorem koszulScalar_smul_first
    (g : SmoothRiemannianMetric I M)
    {f : M -> Real} (X Y Z : (p : M) -> TangentSpace I p) (x : M)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    koszulScalar (I := I) g (f • X) Y Z x =
      f x * koszulScalar (I := I) g X Y Z x := by
  have hZX := mdifferentiableAt_metric_inner (I := I) g hZ hX
  have hXY := mdifferentiableAt_metric_inner (I := I) g hX hY
  unfold koszulScalar
  rw [directionalDerivAlong_smul_fun_left]
  rw [show (fun y : M => g.inner y (Z y) ((f • X) y)) =
      (fun y : M => f y * g.inner y (Z y) (X y)) by
        funext y; simp]
  rw [show (fun y : M => g.inner y ((f • X) y) (Y y)) =
      (fun y : M => f y * g.inner y (X y) (Y y)) by
        funext y; simp]
  unfold directionalDerivAlong
  rw [extDerivFun_mul_at (I := I) (v := Y x) hf hZX]
  rw [extDerivFun_mul_at (I := I) (v := Z x) hf hXY]
  rw [VectorField.mlieBracket_smul_right (I := I) (V := Z) (W := X) hf hX]
  rw [VectorField.mlieBracket_smul_left (I := I) (V := X) (W := Y) hf hX]
  have hdfY :
      NormedSpace.fromTangentSpace (f x)
          (mfderiv I 𝓘(Real, Real) f x (Y x)) =
        extDerivFun (I := I) f x (Y x) := by
    rfl
  have hdfZ :
      NormedSpace.fromTangentSpace (f x)
          (mfderiv I 𝓘(Real, Real) f x (Z x)) =
        extDerivFun (I := I) f x (Z x) := by
    rfl
  simp only [hdfY, hdfZ, map_add, map_smul, map_neg, smul_eq_mul,
    neg_smul, sub_eq_add_neg]
  rw [show (f • X) x = f x • X x by rfl]
  simp only [map_smul]
  rw [show
      (f x • (g.inner x) (X x)) (VectorField.mlieBracket I Y Z x) =
        f x * ((g.inner x) (X x)) (VectorField.mlieBracket I Y Z x) by rfl]
  rw [g.symm x (Y x) (X x), g.symm x (Z x) (X x)]
  ring_nf

omit [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M] in
private theorem koszulScalar_smul_second
    (g : SmoothRiemannianMetric I M)
    {f : M -> Real} (X Y Z : (p : M) -> TangentSpace I p) (x : M)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    koszulScalar (I := I) g X (f • Y) Z x =
      f x * koszulScalar (I := I) g X Y Z x +
        (2 * directionalDerivAlong (I := I) X f x) *
          g.inner x (Y x) (Z x) := by
  have hYZ := mdifferentiableAt_metric_inner (I := I) g hY hZ
  have hXY := mdifferentiableAt_metric_inner (I := I) g hX hY
  unfold koszulScalar
  rw [show (fun y : M => g.inner y ((f • Y) y) (Z y)) =
      (fun y : M => f y * g.inner y (Y y) (Z y)) by
        funext y; simp]
  rw [show (fun y : M => g.inner y (X y) ((f • Y) y)) =
      (fun y : M => f y * g.inner y (X y) (Y y)) by
        funext y; simp]
  rw [directionalDerivAlong_mul_fun (I := I) X x hf hYZ]
  rw [directionalDerivAlong_smul_fun_left]
  rw [directionalDerivAlong_mul_fun (I := I) Z x hf hXY]
  rw [VectorField.mlieBracket_smul_left (I := I) (W := Z) hf hY]
  rw [VectorField.mlieBracket_smul_right (I := I) (V := X) hf hY]
  have hdfZ :
      NormedSpace.fromTangentSpace (f x)
          (mfderiv I 𝓘(Real, Real) f x (Z x)) =
        directionalDerivAlong (I := I) Z f x := by
    rfl
  have hdfX :
      NormedSpace.fromTangentSpace (f x)
          (mfderiv I 𝓘(Real, Real) f x (X x)) =
        directionalDerivAlong (I := I) X f x := by
    rfl
  simp only [hdfZ, hdfX, map_add, map_smul, map_neg, smul_eq_mul,
    neg_smul, sub_eq_add_neg]
  rw [show (f • Y) x = f x • Y x by rfl]
  simp only [map_smul]
  rw [show
      (f x • (g.inner x) (Y x)) (VectorField.mlieBracket I Z X x) =
        f x * ((g.inner x) (Y x)) (VectorField.mlieBracket I Z X x) by rfl]
  rw [g.symm x (Z x) (Y x)]
  ring_nf

omit [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M] in
private theorem koszulScalar_add_third
    (g : SmoothRiemannianMetric I M)
    (X Y Z Z' : (p : M) -> TangentSpace I p) (x : M)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hZ : MDiffAt (T% Z) x) (hZ' : MDiffAt (T% Z') x) :
    koszulScalar (I := I) g X Y (Z + Z') x =
      koszulScalar (I := I) g X Y Z x +
        koszulScalar (I := I) g X Y Z' x := by
  have hYZ := mdifferentiableAt_metric_inner (I := I) g hY hZ
  have hYZ' := mdifferentiableAt_metric_inner (I := I) g hY hZ'
  have hZX := mdifferentiableAt_metric_inner (I := I) g hZ hX
  have hZ'X := mdifferentiableAt_metric_inner (I := I) g hZ' hX
  have hXY := mdifferentiableAt_metric_inner (I := I) g hX hY
  unfold koszulScalar
  rw [show (fun y : M => g.inner y (Y y) ((Z + Z') y)) =
      (fun y : M => g.inner y (Y y) (Z y)) +
        (fun y : M => g.inner y (Y y) (Z' y)) by
        funext y; simp [Pi.add_apply]]
  rw [directionalDerivAlong_add_fun (I := I) X x hYZ hYZ']
  rw [show (fun y : M => g.inner y ((Z + Z') y) (X y)) =
      (fun y : M => g.inner y (Z y) (X y)) +
        (fun y : M => g.inner y (Z' y) (X y)) by
        funext y; simp [Pi.add_apply]]
  rw [directionalDerivAlong_add_fun (I := I) Y x hZX hZ'X]
  rw [directionalDerivAlong_add_left]
  rw [VectorField.mlieBracket_add_right (I := I) (V := Y) hZ hZ']
  rw [VectorField.mlieBracket_add_left (I := I) (W := X) hZ hZ']
  simp [Pi.add_apply, map_add, ContinuousLinearMap.add_apply]
  abel_nf

omit [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M] in
private theorem koszulScalar_smul_third
    (g : SmoothRiemannianMetric I M)
    {f : M -> Real} (X Y Z : (p : M) -> TangentSpace I p) (x : M)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    koszulScalar (I := I) g X Y (f • Z) x =
      f x * koszulScalar (I := I) g X Y Z x := by
  have hYZ := mdifferentiableAt_metric_inner (I := I) g hY hZ
  have hZX := mdifferentiableAt_metric_inner (I := I) g hZ hX
  have hXY := mdifferentiableAt_metric_inner (I := I) g hX hY
  unfold koszulScalar
  rw [show (fun y : M => g.inner y (Y y) ((f • Z) y)) =
      (fun y : M => f y * g.inner y (Y y) (Z y)) by
        funext y; simp]
  rw [show (fun y : M => g.inner y ((f • Z) y) (X y)) =
      (fun y : M => f y * g.inner y (Z y) (X y)) by
        funext y; simp]
  rw [directionalDerivAlong_mul_fun (I := I) X x hf hYZ]
  rw [directionalDerivAlong_mul_fun (I := I) Y x hf hZX]
  rw [directionalDerivAlong_smul_fun_left]
  rw [VectorField.mlieBracket_smul_right (I := I) (V := Y) hf hZ]
  rw [VectorField.mlieBracket_smul_left (I := I) (W := X) hf hZ]
  have hdfX :
      NormedSpace.fromTangentSpace (f x)
          (mfderiv I 𝓘(Real, Real) f x (X x)) =
        directionalDerivAlong (I := I) X f x := by
    rfl
  have hdfY :
      NormedSpace.fromTangentSpace (f x)
          (mfderiv I 𝓘(Real, Real) f x (Y x)) =
        directionalDerivAlong (I := I) Y f x := by
    rfl
  simp only [hdfX, hdfY, map_add, map_smul, map_neg, smul_eq_mul,
    neg_smul, sub_eq_add_neg]
  rw [show (f • Z) x = f x • Z x by rfl]
  simp only [map_smul]
  rw [show
      (f x • (g.inner x) (Z x)) (VectorField.mlieBracket I X Y x) =
        f x * ((g.inner x) (Z x)) (VectorField.mlieBracket I X Y x) by rfl]
  rw [g.symm x (Y x) (Z x), g.symm x (X x) (Z x)]
  ring_nf

omit [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M] in
private theorem koszulScalar_tensorial_first
    (g : SmoothRiemannianMetric I M)
    (Y Z : (p : M) -> TangentSpace I p) (x : M)
    (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    TensorialAt I E (fun X : (p : M) -> TangentSpace I p =>
      koszulScalar (I := I) g X Y Z x) x where
  smul := by
    intro f X hf hX
    simpa [smul_eq_mul] using
      koszulScalar_smul_first (I := I) g X Y Z x hf hX hY hZ
  add := by
    intro X X' hX hX'
    exact koszulScalar_add_first (I := I) g X X' Y Z x hX hX' hY hZ

omit [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M] in
private theorem koszulScalar_tensorial_third
    (g : SmoothRiemannianMetric I M)
    (X Y : (p : M) -> TangentSpace I p) (x : M)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    TensorialAt I E (fun Z : (p : M) -> TangentSpace I p =>
      koszulScalar (I := I) g X Y Z x) x where
  smul := by
    intro f Z hf hZ
    simpa [smul_eq_mul] using
      koszulScalar_smul_third (I := I) g X Y Z x hf hX hY hZ
  add := by
    intro Z Z' hZ hZ'
    exact koszulScalar_add_third (I := I) g X Y Z Z' x hX hY hZ hZ'








def koszulCovectorField
    (g : SmoothRiemannianMetric I M)
    (X Y : (p : M) -> TangentSpace I p) (x : M) :
    Module.Dual Real (TangentSpace I x) :=
  let B : Module.Basis (Fin (Module.finrank Real (TangentSpace I x))) Real
      (TangentSpace I x) := Module.finBasis Real (TangentSpace I x)
  ∑ i : Fin (Module.finrank Real (TangentSpace I x)),
    ((1 / 2 : Real) *
      koszulScalar (I := I) g X Y (tangentConstAt (I := I) x (B i)) x) •
        (B.coord i)


def koszulNablaField
    (g : SmoothRiemannianMetric I M)
    (X Y : (p : M) -> TangentSpace I p) (x : M) :
    TangentSpace I x :=
  metricSharp (I := I) g x (koszulCovectorField (I := I) g X Y x)

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
@[simp] theorem koszulNablaField_inner_eq_covector
    (g : SmoothRiemannianMetric I M)
    (X Y : (p : M) -> TangentSpace I p) (x : M)
    (Z : TangentSpace I x) :
    g.inner x (koszulNablaField (I := I) g X Y x) Z =
      koszulCovectorField (I := I) g X Y x Z := by
  unfold koszulNablaField
  exact inner_metricSharp (I := I) g x
    (koszulCovectorField (I := I) g X Y x) Z

omit [SigmaCompactSpace M] [T2Space M] in
private theorem koszulCovectorField_smul_first
    (g : SmoothRiemannianMetric I M)
    {f : M -> Real} (X Y : (p : M) -> TangentSpace I p) (x : M)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    koszulCovectorField (I := I) g (f • X) Y x =
      f x • koszulCovectorField (I := I) g X Y x := by
  ext v
  unfold koszulCovectorField
  simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply,
    smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hZi :
      MDiffAt (T% (tangentConstAt (I := I) x
        ((Module.finBasis Real (TangentSpace I x)) i) :
          (p : M) -> TangentSpace I p)) x :=
    mdifferentiableAt_tangentConstAt_self (I := I) x
      ((Module.finBasis Real (TangentSpace I x)) i)
  rw [koszulScalar_smul_first (I := I) g X Y
    (tangentConstAt (I := I) x
      ((Module.finBasis Real (TangentSpace I x)) i)) x hf hX hY hZi]
  ring

omit [SigmaCompactSpace M] [T2Space M] in
private theorem koszulCovectorField_add_first
    (g : SmoothRiemannianMetric I M)
    (X X' Y : (p : M) -> TangentSpace I p) (x : M)
    (hX : MDiffAt (T% X) x) (hX' : MDiffAt (T% X') x)
    (hY : MDiffAt (T% Y) x) :
    koszulCovectorField (I := I) g (X + X') Y x =
      koszulCovectorField (I := I) g X Y x +
        koszulCovectorField (I := I) g X' Y x := by
  ext v
  unfold koszulCovectorField
  simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply,
    LinearMap.add_apply, smul_eq_mul]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hZi :
      MDiffAt (T% (tangentConstAt (I := I) x
        ((Module.finBasis Real (TangentSpace I x)) i) :
          (p : M) -> TangentSpace I p)) x :=
    mdifferentiableAt_tangentConstAt_self (I := I) x
      ((Module.finBasis Real (TangentSpace I x)) i)
  rw [koszulScalar_add_first (I := I) g X X' Y
    (tangentConstAt (I := I) x
      ((Module.finBasis Real (TangentSpace I x)) i)) x hX hX' hY hZi]
  ring

omit [SigmaCompactSpace M] [T2Space M] in
private theorem koszulNablaField_smul_first
    (g : SmoothRiemannianMetric I M)
    {f : M -> Real} (X Y : (p : M) -> TangentSpace I p) (x : M)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    koszulNablaField (I := I) g (f • X) Y x =
      f x • koszulNablaField (I := I) g X Y x := by
  unfold koszulNablaField metricSharp
  rw [koszulCovectorField_smul_first (I := I) g X Y x hf hX hY]
  exact LinearEquiv.map_smul (metricFlatEquiv (I := I) g x).symm
    (f x) (koszulCovectorField (I := I) g X Y x)

omit [SigmaCompactSpace M] [T2Space M] in
private theorem koszulNablaField_add_first
    (g : SmoothRiemannianMetric I M)
    (X X' Y : (p : M) -> TangentSpace I p) (x : M)
    (hX : MDiffAt (T% X) x) (hX' : MDiffAt (T% X') x)
    (hY : MDiffAt (T% Y) x) :
    koszulNablaField (I := I) g (X + X') Y x =
      koszulNablaField (I := I) g X Y x +
        koszulNablaField (I := I) g X' Y x := by
  unfold koszulNablaField metricSharp
  rw [koszulCovectorField_add_first (I := I) g X X' Y x hX hX' hY]
  exact LinearEquiv.map_add (metricFlatEquiv (I := I) g x).symm
    (koszulCovectorField (I := I) g X Y x)
    (koszulCovectorField (I := I) g X' Y x)

omit [SigmaCompactSpace M] [T2Space M] in
private theorem koszulCovectorField_add_second
    (g : SmoothRiemannianMetric I M)
    (X Y Y' : (p : M) -> TangentSpace I p) (x : M)
    (hX : MDiffAt (T% X) x)
    (hY : MDiffAt (T% Y) x) (hY' : MDiffAt (T% Y') x) :
    koszulCovectorField (I := I) g X (Y + Y') x =
      koszulCovectorField (I := I) g X Y x +
        koszulCovectorField (I := I) g X Y' x := by
  ext v
  unfold koszulCovectorField
  simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply,
    LinearMap.add_apply, smul_eq_mul]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hZi :
      MDiffAt (T% (tangentConstAt (I := I) x
        ((Module.finBasis Real (TangentSpace I x)) i) :
          (p : M) -> TangentSpace I p)) x :=
    mdifferentiableAt_tangentConstAt_self (I := I) x
      ((Module.finBasis Real (TangentSpace I x)) i)
  rw [koszulScalar_add_second (I := I) g X Y Y'
    (tangentConstAt (I := I) x
      ((Module.finBasis Real (TangentSpace I x)) i)) x hX hY hY' hZi]
  ring

omit [SigmaCompactSpace M] [T2Space M] in
private theorem koszulNablaField_add_second
    (g : SmoothRiemannianMetric I M)
    (X Y Y' : (p : M) -> TangentSpace I p) (x : M)
    (hX : MDiffAt (T% X) x)
    (hY : MDiffAt (T% Y) x) (hY' : MDiffAt (T% Y') x) :
    koszulNablaField (I := I) g X (Y + Y') x =
      koszulNablaField (I := I) g X Y x +
        koszulNablaField (I := I) g X Y' x := by
  unfold koszulNablaField metricSharp
  rw [koszulCovectorField_add_second (I := I) g X Y Y' x hX hY hY']
  exact LinearEquiv.map_add (metricFlatEquiv (I := I) g x).symm
    (koszulCovectorField (I := I) g X Y x)
    (koszulCovectorField (I := I) g X Y' x)

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem metric_inner_sum_basis_coord
    (g : SmoothRiemannianMetric I M) {x : M}
    (B : Module.Basis (Fin (Module.finrank Real (TangentSpace I x))) Real
      (TangentSpace I x))
    (Y v : TangentSpace I x) :
    (∑ i, g.inner x Y (B i) * (B.coord i) v) = g.inner x Y v := by
  calc
    (∑ i, g.inner x Y (B i) * (B.coord i) v)
        = ∑ i, (B.repr v i) * g.inner x Y (B i) := by
          apply Finset.sum_congr rfl
          intro i _
          simp [B.coord_apply, mul_comm]
    _ = g.inner x Y (∑ i, (B.repr v i) • B i) := by
          calc
            (∑ i, (B.repr v i) * g.inner x Y (B i))
                = ∑ i, g.inner x Y ((B.repr v i) • B i) := by
                  apply Finset.sum_congr rfl
                  intro i _
                  simp [map_smul, smul_eq_mul]
            _ = g.inner x Y (∑ i, (B.repr v i) • B i) := by
                  rw [map_sum]
    _ = g.inner x Y v := by
          rw [B.sum_repr v]

omit [SigmaCompactSpace M] [T2Space M] in
private theorem koszulCovectorField_smul_second
    (g : SmoothRiemannianMetric I M)
    {f : M -> Real} (X Y : (p : M) -> TangentSpace I p) (x : M)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    koszulCovectorField (I := I) g X (f • Y) x =
      f x • koszulCovectorField (I := I) g X Y x +
        directionalDerivAlong (I := I) X f x • metricFlatLinear (I := I) g x (Y x) := by
  ext v
  unfold koszulCovectorField
  let B : Module.Basis (Fin (Module.finrank Real (TangentSpace I x))) Real
      (TangentSpace I x) := Module.finBasis Real (TangentSpace I x)
  simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply,
    LinearMap.add_apply, smul_eq_mul, metricFlatLinear_apply]
  rw [Finset.mul_sum]
  have hbasis :
      (∑ i : Fin (Module.finrank Real (TangentSpace I x)),
          g.inner x (Y x) ((Module.finBasis Real (TangentSpace I x)) i) *
            ((Module.finBasis Real (TangentSpace I x)).coord i) v) =
        g.inner x (Y x) v :=
    metric_inner_sum_basis_coord (I := I) g
      (Module.finBasis Real (TangentSpace I x)) (Y x) v
  rw [← hbasis]
  rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hZi :
      MDiffAt (T% (tangentConstAt (I := I) x
        ((Module.finBasis Real (TangentSpace I x)) i) :
          (p : M) -> TangentSpace I p)) x :=
    mdifferentiableAt_tangentConstAt_self (I := I) x
      ((Module.finBasis Real (TangentSpace I x)) i)
  rw [koszulScalar_smul_second (I := I) g X Y
    (tangentConstAt (I := I) x
      ((Module.finBasis Real (TangentSpace I x)) i)) x hf hX hY hZi]
  rw [tangentConstAt_self]
  ring_nf

omit [SigmaCompactSpace M] [T2Space M] in
private theorem koszulNablaField_smul_second
    (g : SmoothRiemannianMetric I M)
    {f : M -> Real} (X Y : (p : M) -> TangentSpace I p) (x : M)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    koszulNablaField (I := I) g X (f • Y) x =
      f x • koszulNablaField (I := I) g X Y x +
        directionalDerivAlong (I := I) X f x • Y x := by
  unfold koszulNablaField metricSharp
  rw [koszulCovectorField_smul_second (I := I) g X Y x hf hX hY]
  rw [LinearEquiv.map_add, LinearEquiv.map_smul]
  congr 1
  change (metricFlatEquiv (I := I) g x).symm
      (directionalDerivAlong (I := I) X f x • metricFlatLinear (I := I) g x (Y x)) =
    directionalDerivAlong (I := I) X f x • Y x
  rw [LinearEquiv.map_smul]
  congr 1
  exact LinearEquiv.symm_apply_apply (metricFlatEquiv (I := I) g x) (Y x)

omit [SigmaCompactSpace M] [T2Space M] in
private theorem koszulNablaField_tensorial_first
    (g : SmoothRiemannianMetric I M)
    (Y : (p : M) -> TangentSpace I p) (x : M)
    (hY : MDiffAt (T% Y) x) :
    TensorialAt I E (fun X : (p : M) -> TangentSpace I p =>
      koszulNablaField (I := I) g X Y x) x where
  smul := by
    intro f X hf hX
    exact koszulNablaField_smul_first (I := I) g X Y x hf hX hY
  add := by
    intro X X' hX hX'
    exact koszulNablaField_add_first (I := I) g X X' Y x hX hX' hY






def koszulNablaAt
    (g : SmoothRiemannianMetric I M)
    (Y : (p : M) -> TangentSpace I p) (x : M)
    (v : TangentSpace I x) : TangentSpace I x :=
  koszulNablaField (I := I) g (tangentConstAt (I := I) x v) Y x






def KoszulCovectorCorrectAt
    (g : SmoothRiemannianMetric I M)
    (X Y : (p : M) -> TangentSpace I p) (x : M) : Prop :=
  forall Z : (p : M) -> TangentSpace I p,
    MDiffAt (T% Z) x ->
      koszulCovectorField (I := I) g X Y x (Z x) =
        (1 / 2 : Real) * koszulScalar (I := I) g X Y Z x

omit [SigmaCompactSpace M] [T2Space M] in
theorem koszulCovectorField_apply_of_mdiff
    (g : SmoothRiemannianMetric I M)
    (X Y Z : (p : M) -> TangentSpace I p) (x : M)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hZ : MDiffAt (T% Z) x) :
    koszulCovectorField (I := I) g X Y x (Z x) =
      (1 / 2 : Real) * koszulScalar (I := I) g X Y Z x := by
  classical
  let B : Module.Basis (Fin (Module.finrank Real (TangentSpace I x))) Real
      (TangentSpace I x) := Module.finBasis Real (TangentSpace I x)
  let Φ : ((p : M) -> TangentSpace I p) -> Real :=
    fun Z => (1 / 2 : Real) * koszulScalar (I := I) g X Y Z x
  have hΦ : TensorialAt I E Φ x := by
    refine { smul := ?_, add := ?_ }
    · intro f Z hf hZ
      dsimp [Φ]
      rw [koszulScalar_smul_third (I := I) g X Y Z x hf hX hY hZ]
      ring
    · intro Z Z' hZ hZ'
      dsimp [Φ]
      rw [koszulScalar_add_third (I := I) g X Y Z Z' x hX hY hZ hZ']
      ring
  have hEq :
      koszulCovectorField (I := I) g X Y x =
        TensorialAt.mkHom (I := I) (F := E) Φ x hΦ := by
    apply LinearMap.ext
    intro v
    rw [← B.sum_repr v]
    rw [map_sum, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul, map_smul]
    congr 1
    have hmk := TensorialAt.mkHom_apply (I := I) (F := E) hΦ
      (mdifferentiableAt_tangentConstAt_self (I := I) x (B i))
    rw [tangentConstAt_self] at hmk
    have hmk' :
        (TensorialAt.mkHom (I := I) (F := E) Φ x hΦ) (B i) =
          (1 / 2 : Real) * koszulScalar (I := I) g X Y
            (tangentConstAt (I := I) x (B i)) x := by
      simpa [Φ] using hmk
    change (koszulCovectorField (I := I) g X Y x) (B i) =
      (TensorialAt.mkHom (I := I) (F := E) Φ x hΦ) (B i)
    rw [hmk']
    simp [koszulCovectorField, B, Finsupp.single_apply]
  rw [hEq]
  exact TensorialAt.mkHom_apply (I := I) (F := E) hΦ hZ

omit [SigmaCompactSpace M] [T2Space M] in
theorem koszulCovectorCorrectAt_of_mdiff
    (g : SmoothRiemannianMetric I M)
    (X Y : (p : M) -> TangentSpace I p) (x : M)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    KoszulCovectorCorrectAt (I := I) g X Y x := by
  intro Z hZ
  exact koszulCovectorField_apply_of_mdiff (I := I) g X Y Z x hX hY hZ

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem koszulNablaField_eval_of_covector_correct
    (g : SmoothRiemannianMetric I M)
    (X Y Z : (p : M) -> TangentSpace I p) (x : M)
    (hcorrect : KoszulCovectorCorrectAt (I := I) g X Y x)
    (hZ : MDiffAt (T% Z) x) :
    g.inner x (koszulNablaField (I := I) g X Y x) (Z x) =
      (1 / 2 : Real) * koszulScalar (I := I) g X Y Z x := by
  rw [koszulNablaField_inner_eq_covector]
  exact hcorrect Z hZ

omit [SigmaCompactSpace M] [T2Space M] in
theorem koszulNablaField_inner_eq_koszulScalar
    (g : SmoothRiemannianMetric I M)
    (X Y Z : (p : M) -> TangentSpace I p) (x : M)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hZ : MDiffAt (T% Z) x) :
    g.inner x (koszulNablaField (I := I) g X Y x) (Z x) =
      (1 / 2 : Real) * koszulScalar (I := I) g X Y Z x :=
  koszulNablaField_eval_of_covector_correct (I := I) g X Y Z x
    (koszulCovectorCorrectAt_of_mdiff (I := I) g X Y x hX hY) hZ

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem koszulScalar_pair_sum
    (g : SmoothRiemannianMetric I M)
    (X Y Z : (p : M) -> TangentSpace I p) (x : M) :
    (1 / 2 : Real) * koszulScalar (I := I) g X Y Z x +
      (1 / 2 : Real) * koszulScalar (I := I) g X Z Y x =
        directionalDerivAlong (I := I) X (fun y : M => g.inner y (Y y) (Z y)) x := by
  unfold koszulScalar
  rw [show (fun y : M => g.inner y (Z y) (Y y)) =
      (fun y : M => g.inner y (Y y) (Z y)) by
      funext y; exact g.symm y (Z y) (Y y)]
  rw [show (fun y : M => g.inner y (Y y) (X y)) =
      (fun y : M => g.inner y (X y) (Y y)) by
      funext y; exact g.symm y (Y y) (X y)]
  rw [show (fun y : M => g.inner y (X y) (Z y)) =
      (fun y : M => g.inner y (Z y) (X y)) by
      funext y; exact g.symm y (X y) (Z y)]
  rw [VectorField.mlieBracket_swap_apply (I := I) (V := Z) (W := Y) (x := x)]
  rw [VectorField.mlieBracket_swap_apply (I := I) (V := Y) (W := X) (x := x)]
  rw [VectorField.mlieBracket_swap_apply (I := I) (V := X) (W := Z) (x := x)]
  simp only [map_neg]
  ring



omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem koszulScalar_swap_sub
    (g : SmoothRiemannianMetric I M)
    (X Y Z : (p : M) -> TangentSpace I p) (x : M) :
    (1 / 2 : Real) * koszulScalar (I := I) g X Y Z x -
      (1 / 2 : Real) * koszulScalar (I := I) g Y X Z x =
        g.inner x (VectorField.mlieBracket I X Y x) (Z x) := by
  unfold koszulScalar
  rw [show (fun y : M => g.inner y (X y) (Z y)) =
      (fun y : M => g.inner y (Z y) (X y)) by
      funext y
      exact g.symm y (X y) (Z y)]
  rw [show (fun y : M => g.inner y (Z y) (Y y)) =
      (fun y : M => g.inner y (Y y) (Z y)) by
      funext y
      exact g.symm y (Z y) (Y y)]
  rw [show (fun y : M => g.inner y (Y y) (X y)) =
      (fun y : M => g.inner y (X y) (Y y)) by
      funext y
      exact g.symm y (Y y) (X y)]
  rw [VectorField.mlieBracket_swap_apply (I := I) (V := Z) (W := X) (x := x)]
  rw [VectorField.mlieBracket_swap_apply (I := I) (V := Z) (W := Y) (x := x)]
  rw [VectorField.mlieBracket_swap_apply (I := I) (V := Y) (W := X) (x := x)]
  simp only [map_neg]
  rw [g.symm x (VectorField.mlieBracket I X Y x) (Z x)]
  ring







omit [SigmaCompactSpace M] [T2Space M] in
theorem koszulNablaField_eq_of_first_eq_at
    (g : SmoothRiemannianMetric I M)
    (X X' Y : (p : M) -> TangentSpace I p) (x : M)
    (hX : MDiffAt (T% X) x) (hX' : MDiffAt (T% X') x)
    (hY : MDiffAt (T% Y) x)
    (hxx : X x = X' x) :
    koszulNablaField (I := I) g X Y x =
      koszulNablaField (I := I) g X' Y x := by
  unfold koszulNablaField
  congr 1
  ext v
  unfold koszulCovectorField
  let B : Module.Basis (Fin (Module.finrank Real (TangentSpace I x))) Real
      (TangentSpace I x) := Module.finBasis Real (TangentSpace I x)
  simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply]
  apply Finset.sum_congr rfl
  intro i _
  have hZi :
      MDiffAt (T% (tangentConstAt (I := I) x (B i) :
        (p : M) -> TangentSpace I p)) x :=
    mdifferentiableAt_tangentConstAt_self (I := I) x (B i)
  have hK :
      koszulScalar (I := I) g X Y
          (tangentConstAt (I := I) x (B i)) x =
        koszulScalar (I := I) g X' Y
          (tangentConstAt (I := I) x (B i)) x :=
    TensorialAt.pointwise
      (I := I) (F := E)
      (koszulScalar_tensorial_first (I := I) g Y
        (tangentConstAt (I := I) x (B i)) x hY hZi)
      hX hX' hxx
  rw [hK]





omit [SigmaCompactSpace M] [T2Space M] in
theorem koszulNablaAt_eq_of_extension
    (g : SmoothRiemannianMetric I M)
    (X Y : (p : M) -> TangentSpace I p) (x : M)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (v : TangentSpace I x) (hXx : X x = v) :
    koszulNablaAt (I := I) g Y x v =
      koszulNablaField (I := I) g X Y x := by
  unfold koszulNablaAt
  have hconst :
      (tangentConstAt (I := I) x v : (p : M) -> TangentSpace I p) x =
        X x := by
    rw [tangentConstAt_self]
    exact hXx.symm
  exact koszulNablaField_eq_of_first_eq_at (I := I) g
    (tangentConstAt (I := I) x v) X Y x
    (mdifferentiableAt_tangentConstAt_self (I := I) x v) hX hY hconst








def leviCivitaConnectionCandidateAt
    (g : SmoothRiemannianMetric I M)
    (Y : (p : M) -> TangentSpace I p) (x : M) :
    TangentSpace I x →L[Real] TangentSpace I x := by
  let B : Module.Basis (Fin (Module.finrank Real (TangentSpace I x))) Real
      (TangentSpace I x) := Module.finBasis Real (TangentSpace I x)
  let W : Fin (Module.finrank Real (TangentSpace I x)) -> TangentSpace I x := fun i =>
    koszulNablaField (I := I) g (tangentConstAt (I := I) x (B i)) Y x
  exact LinearMap.toContinuousLinearMap
    (B.constr Real W)

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
@[simp] theorem leviCivitaConnectionCandidateAt_apply_basis
    (g : SmoothRiemannianMetric I M)
    (Y : (p : M) -> TangentSpace I p) (x : M)
    (i : Fin (Module.finrank Real (TangentSpace I x))) :
    leviCivitaConnectionCandidateAt (I := I) g Y x
        ((Module.finBasis Real (TangentSpace I x)) i) =
      koszulNablaField (I := I) g
        (tangentConstAt (I := I) x ((Module.finBasis Real (TangentSpace I x)) i)) Y x := by
  classical
  unfold leviCivitaConnectionCandidateAt
  let B : Module.Basis (Fin (Module.finrank Real (TangentSpace I x))) Real
      (TangentSpace I x) := Module.finBasis Real (TangentSpace I x)
  let W : Fin (Module.finrank Real (TangentSpace I x)) -> TangentSpace I x := fun i =>
    koszulNablaField (I := I) g (tangentConstAt (I := I) x (B i)) Y x
  change LinearMap.toContinuousLinearMap (B.constr Real W) (B i) = W i
  simp [B.constr_basis (S := Real) W i]

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
@[simp] theorem leviCivitaConnectionCandidateAt_basis_agreesWithField
    (g : SmoothRiemannianMetric I M)
    (Y : (p : M) -> TangentSpace I p) (x : M)
    (i : Fin (Module.finrank Real (TangentSpace I x))) :
    leviCivitaConnectionCandidateAt (I := I) g Y x
        ((Module.finBasis Real (TangentSpace I x)) i) =
      koszulNablaAt (I := I) g Y x
        ((Module.finBasis Real (TangentSpace I x)) i) := by
  rw [leviCivitaConnectionCandidateAt_apply_basis]
  rfl






omit [SigmaCompactSpace M] [T2Space M] in
theorem leviCivitaConnectionCandidateAt_agreesWithField
    (g : SmoothRiemannianMetric I M)
    (X Y : (p : M) -> TangentSpace I p) (x : M)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    leviCivitaConnectionCandidateAt (I := I) g Y x (X x) =
      koszulNablaField (I := I) g X Y x := by
  classical
  let Φ : ((p : M) -> TangentSpace I p) -> TangentSpace I x :=
    fun X => koszulNablaField (I := I) g X Y x
  have hΦ : TensorialAt I E Φ x :=
    koszulNablaField_tensorial_first (I := I) g Y x hY
  let L : TangentSpace I x →L[Real] TangentSpace I x :=
    TensorialAt.mkHom (I := I) (F := E) Φ x hΦ
  have hLX : L (X x) = koszulNablaField (I := I) g X Y x := by
    simpa [Φ, L] using TensorialAt.mkHom_apply (I := I) (F := E) hΦ hX
  rw [← hLX]
  let B : Module.Basis (Fin (Module.finrank Real (TangentSpace I x))) Real
      (TangentSpace I x) := Module.finBasis Real (TangentSpace I x)
  rw [← B.sum_repr (X x)]
  rw [map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, map_smul]
  congr 1
  rw [leviCivitaConnectionCandidateAt_apply_basis]
  have hZi :
      MDiffAt (T% (tangentConstAt (I := I) x (B i) :
        (p : M) -> TangentSpace I p)) x :=
    mdifferentiableAt_tangentConstAt_self (I := I) x (B i)
  have hLi : L (B i) =
      koszulNablaField (I := I) g
        (tangentConstAt (I := I) x (B i)) Y x := by
    have hmk := TensorialAt.mkHom_apply (I := I) (F := E) hΦ hZi
    rw [tangentConstAt_self] at hmk
    simpa [Φ, L] using hmk
  exact hLi.symm



omit [SigmaCompactSpace M] [T2Space M] in
theorem leviCivitaConnectionCandidateAt_agreesWithDescended
    (g : SmoothRiemannianMetric I M)
    (Y : (p : M) -> TangentSpace I p) (x : M)
    (hY : MDiffAt (T% Y) x) (v : TangentSpace I x) :
    leviCivitaConnectionCandidateAt (I := I) g Y x v =
      koszulNablaAt (I := I) g Y x v := by
  have hfield := leviCivitaConnectionCandidateAt_agreesWithField
    (I := I) g (tangentConstAt (I := I) x v) Y x
    (mdifferentiableAt_tangentConstAt_self (I := I) x v) hY
  unfold koszulNablaAt
  convert hfield using 1
  exact congrArg (leviCivitaConnectionCandidateAt (I := I) g Y x)
    (tangentConstAt_self (I := I) x v).symm






def leviCivitaConnectionOfMetric
    (g : SmoothRiemannianMetric I M) :
    CovariantDerivative I E (TangentSpace I : M -> Type _) where
  toFun := fun Y x => leviCivitaConnectionCandidateAt (I := I) g Y x
  isCovariantDerivativeOnUniv := by
    refine
      { add := ?_
        leibniz := ?_ }
    · intro Y Y' x hY hY' _hx
      ext v
      rw [ContinuousLinearMap.add_apply]
      rw [leviCivitaConnectionCandidateAt_agreesWithDescended
        (I := I) g (Y + Y') x (mdifferentiableAt_add_section hY hY') v]
      rw [leviCivitaConnectionCandidateAt_agreesWithDescended
        (I := I) g Y x hY v]
      rw [leviCivitaConnectionCandidateAt_agreesWithDescended
        (I := I) g Y' x hY' v]
      unfold koszulNablaAt
      exact koszulNablaField_add_second (I := I) g
        (tangentConstAt (I := I) x v) Y Y' x
        (mdifferentiableAt_tangentConstAt_self (I := I) x v) hY hY'
    · intro Y f x hY hf _hx
      ext v
      rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.smulRight_apply]
      rw [leviCivitaConnectionCandidateAt_agreesWithDescended
        (I := I) g (f • Y) x (hf.smul_section hY) v]
      rw [leviCivitaConnectionCandidateAt_agreesWithDescended
        (I := I) g Y x hY v]
      unfold koszulNablaAt
      rw [koszulNablaField_smul_second (I := I) g
        (tangentConstAt (I := I) x v) Y x hf
        (mdifferentiableAt_tangentConstAt_self (I := I) x v) hY]
      congr 1
      unfold directionalDerivAlong
      rw [tangentConstAt_self]

omit [SigmaCompactSpace M] [T2Space M] in
@[simp] theorem leviCivitaConnectionOfMetric_apply
    (g : SmoothRiemannianMetric I M)
    (Y : (p : M) -> TangentSpace I p) (x : M) :
    leviCivitaConnectionOfMetric (I := I) g Y x =
      leviCivitaConnectionCandidateAt (I := I) g Y x := by
  rfl

omit [SigmaCompactSpace M] [T2Space M] in
theorem leviCivitaConnectionOfMetric_apply_descended
    (g : SmoothRiemannianMetric I M)
    (Y : (p : M) -> TangentSpace I p) (x : M)
    (hY : MDiffAt (T% Y) x) (v : TangentSpace I x) :
    leviCivitaConnectionOfMetric (I := I) g Y x v =
      koszulNablaAt (I := I) g Y x v := by
  rw [leviCivitaConnectionOfMetric_apply]
  exact leviCivitaConnectionCandidateAt_agreesWithDescended (I := I) g Y x hY v

omit [SigmaCompactSpace M] [T2Space M] in
theorem leviCivitaConnectionOfMetric_inner_eq_koszulScalar
    (g : SmoothRiemannianMetric I M)
    (X Y Z : (p : M) -> TangentSpace I p) (x : M)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hZ : MDiffAt (T% Z) x) :
    g.inner x ((leviCivitaConnectionOfMetric (I := I) g Y x) (X x)) (Z x) =
      (1 / 2 : Real) * koszulScalar (I := I) g X Y Z x := by
  rw [leviCivitaConnectionOfMetric_apply_descended (I := I) g Y x hY (X x)]
  rw [koszulNablaAt_eq_of_extension (I := I) g X Y x hX hY (X x) rfl]
  exact koszulNablaField_inner_eq_koszulScalar (I := I) g X Y Z x hX hY hZ







omit [SigmaCompactSpace M] [T2Space M] in
theorem leviCivitaConnectionOfMetric_inner_eq_koszulScalar_tangent
    (g : SmoothRiemannianMetric I M)
    (X Y : (p : M) -> TangentSpace I p) (x : M)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (v : TangentSpace I x) :
    g.inner x ((leviCivitaConnectionOfMetric (I := I) g Y x) (X x)) v =
      (1 / 2 : Real) *
        koszulScalar (I := I) g X Y (tangentConstAt (I := I) x v) x := by
  have hZ :
      MDiffAt
        (T% (tangentConstAt (I := I) x v : (p : M) -> TangentSpace I p)) x :=
    mdifferentiableAt_tangentConstAt_self (I := I) x v
  have h := leviCivitaConnectionOfMetric_inner_eq_koszulScalar
    (I := I) g X Y (tangentConstAt (I := I) x v) x hX hY hZ
  rw [tangentConstAt_self] at h
  exact h


omit [SigmaCompactSpace M] [T2Space M] in
theorem leviCivitaConnectionOfMetric_isMetricCompatible
    (g : SmoothRiemannianMetric I M) :
    IsMetricCompatible_gen (I := I) (leviCivitaConnectionOfMetric (I := I) g) g := by
  intro x X Y Z hX hY hZ
  change directionalDerivAlong (I := I) X
      (fun y : M => g.inner y (Y y) (Z y)) x =
    g.inner x ((leviCivitaConnectionOfMetric (I := I) g Y x) (X x)) (Z x) +
      g.inner x (Y x) ((leviCivitaConnectionOfMetric (I := I) g Z x) (X x))
  have hXYZ := leviCivitaConnectionOfMetric_inner_eq_koszulScalar
    (I := I) g X Y Z x hX hY hZ
  have hXZY := leviCivitaConnectionOfMetric_inner_eq_koszulScalar
    (I := I) g X Z Y x hX hZ hY
  calc
    directionalDerivAlong (I := I) X
        (fun y : M => g.inner y (Y y) (Z y)) x
        = (1 / 2 : Real) * koszulScalar (I := I) g X Y Z x +
            (1 / 2 : Real) * koszulScalar (I := I) g X Z Y x := by
          exact (koszulScalar_pair_sum (I := I) g X Y Z x).symm
    _ = g.inner x ((leviCivitaConnectionOfMetric (I := I) g Y x) (X x)) (Z x) +
          g.inner x ((leviCivitaConnectionOfMetric (I := I) g Z x) (X x)) (Y x) := by
          rw [← hXYZ, ← hXZY]
    _ = g.inner x ((leviCivitaConnectionOfMetric (I := I) g Y x) (X x)) (Z x) +
          g.inner x (Y x) ((leviCivitaConnectionOfMetric (I := I) g Z x) (X x)) := by
          rw [g.symm x ((leviCivitaConnectionOfMetric (I := I) g Z x) (X x)) (Y x)]

end

end DifferentialGeometry.Integral.Connection
