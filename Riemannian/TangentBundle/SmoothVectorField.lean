import Mathlib.Geometry.Manifold.ContMDiff.Defs
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Riemannian.TangentBundle.SmoothSection
import Riemannian.TangentBundle.Smoothness

/-!
# `SmoothVectorField` — bundled smooth tangent vector fields

Bundles a `Π y : M, TangentSpace I y` with its `C^∞` smoothness witness.
Eliminates the need for client code to plumb `ContMDiff` premises through
every framework theorem.

## Algebraic structure

* `Add` / `Sub` / `Zero` / `Neg`
* Scalar-function multiplication via `smul`
* `CoeFun` to the raw `Π y, TangentSpace I y`

Closure lemmas reuse `OpenGALib.TangentSmoothAt.*` from
`Riemannian.TangentBundle.SmoothSection`.

## Usage

```
theorem foo (X Y : SmoothVectorField I M) (x : M) : ... := ...
```

Smoothness lives in the type. No premise plumbing.
-/

open Bundle
open scoped ContDiff Manifold

namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- A **smooth tangent vector field** on `M`: a `Π`-section of the tangent
bundle whose total-space form is `C^∞`. -/
structure SmoothVectorField (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] where
  /-- The underlying section. -/
  toFun : Π y : M, TangentSpace I y
  /-- Smoothness witness for the bundle section. -/
  smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
    (fun y => (⟨y, toFun y⟩ : TangentBundle I M))

namespace SmoothVectorField

/-- A `SmoothVectorField` coerces to its underlying section. -/
instance : CoeFun (SmoothVectorField I M) fun _ => Π y : M, TangentSpace I y :=
  ⟨toFun⟩

@[simp] lemma coe_mk (f : Π y : M, TangentSpace I y) (h) :
    ⇑(⟨f, h⟩ : SmoothVectorField I M) = f := rfl

/-- Pointwise smoothness extracted from the global witness. -/
theorem smoothAt (X : SmoothVectorField I M) (x : M) : OpenGALib.TangentSmoothAt X x :=
  OpenGALib.TangentSmoothAt.mk ((X.smooth x).mdifferentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0))

/-! ## Algebraic structure

Closures via Mathlib's `ContMDiff.{add,neg,sub,smul,const_smul}_section`
in `Mathlib.Geometry.Manifold.VectorBundle.SmoothSection`. -/

/-- The zero vector field. -/
noncomputable def zero : SmoothVectorField I M where
  toFun := fun _ => 0
  smooth := Bundle.contMDiff_zeroSection ℝ (TangentSpace I (M := M)) (n := ∞)

noncomputable instance : Zero (SmoothVectorField I M) := ⟨zero⟩

@[simp] lemma zero_apply (y : M) : (0 : SmoothVectorField I M) y = 0 := rfl

/-- Sum of two smooth vector fields. -/
noncomputable def add (X Y : SmoothVectorField I M) : SmoothVectorField I M where
  toFun := fun y => X y + Y y
  smooth := ContMDiff.add_section X.smooth Y.smooth

noncomputable instance : Add (SmoothVectorField I M) := ⟨add⟩

@[simp] lemma add_apply (X Y : SmoothVectorField I M) (y : M) :
    (X + Y) y = X y + Y y := rfl

/-- Negation of a smooth vector field. -/
noncomputable def neg (X : SmoothVectorField I M) : SmoothVectorField I M where
  toFun := fun y => -X y
  smooth := ContMDiff.neg_section X.smooth

noncomputable instance : Neg (SmoothVectorField I M) := ⟨neg⟩

@[simp] lemma neg_apply (X : SmoothVectorField I M) (y : M) :
    (-X) y = -X y := rfl

/-- Difference of two smooth vector fields. -/
noncomputable def sub (X Y : SmoothVectorField I M) : SmoothVectorField I M where
  toFun := fun y => X y - Y y
  smooth := ContMDiff.sub_section X.smooth Y.smooth

noncomputable instance : Sub (SmoothVectorField I M) := ⟨sub⟩

@[simp] lemma sub_apply (X Y : SmoothVectorField I M) (y : M) :
    (X - Y) y = X y - Y y := rfl

/-- Constant scalar multiplication. -/
noncomputable def constSMul (a : ℝ) (X : SmoothVectorField I M) : SmoothVectorField I M where
  toFun := fun y => a • X y
  smooth := ContMDiff.const_smul_section (a := a) X.smooth

noncomputable instance : SMul ℝ (SmoothVectorField I M) := ⟨constSMul⟩

@[simp] lemma constSMul_apply (a : ℝ) (X : SmoothVectorField I M) (y : M) :
    (a • X) y = a • X y := by
  show (constSMul a X) y = a • X y; rfl

/-- Smooth-scalar-function multiplication: `f • X` for smooth `f : M → ℝ`. -/
noncomputable def smul (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (X : SmoothVectorField I M) : SmoothVectorField I M where
  toFun := fun y => f y • X y
  smooth := ContMDiff.smul_section hf X.smooth

@[simp] lemma smul_apply (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (X : SmoothVectorField I M) (y : M) :
    (smul f hf X) y = f y • X y := rfl

/-! ## Constant section (chart-coherent) -/

/-- Constant `E`-valued section as a `SmoothVectorField`. Requires
`IsLocallyConstantChartedSpace` for the smoothness witness. -/
noncomputable def const [_root_.IsLocallyConstantChartedSpace H M] (v : E) :
    SmoothVectorField I M where
  toFun := fun _ => v
  smooth := TangentBundle.contMDiff_constSection_TangentSpace v

@[simp] lemma const_apply [_root_.IsLocallyConstantChartedSpace H M] (v : E) (y : M) :
    (const (I := I) v) y = v := rfl

end SmoothVectorField

end Riemannian
