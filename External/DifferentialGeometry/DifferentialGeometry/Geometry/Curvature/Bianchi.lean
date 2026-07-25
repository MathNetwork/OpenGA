import DifferentialGeometry.Geometry.Curvature.Components.Basic
import DifferentialGeometry.Geometry.Curvature.Components.Lowering
import DifferentialGeometry.Geometry.Curvature.Components.TraceOneForm
import DifferentialGeometry.Geometry.Curvature.Components.RicciTrace
import DifferentialGeometry.Geometry.Curvature.Components.LocalFrame
import DifferentialGeometry.Geometry.Curvature.Components.Christoffel
import DifferentialGeometry.Geometry.Curvature.Components.RicciIdentity
import DifferentialGeometry.Geometry.Curvature.Riemann.Basic.Field
import DifferentialGeometry.Geometry.Curvature.Riemann.Basic.Pointwise
import DifferentialGeometry.Geometry.Curvature.Riemann.Basic.Sections
import DifferentialGeometry.Geometry.Operator.RoughLaplacian
import DifferentialGeometry.Geometry.Connection.LeviCivita.Basic
import DifferentialGeometry.Geometry.Connection.LeviCivita.Torsion
import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.Connection.Smooth
import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.Connection.Tangent
import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.Connection.Endomorphism

set_option autoImplicit false
set_option linter.style.longLine false










noncomputable section

namespace DifferentialGeometry.Integral.Connection

open Bundle Tensor0SBundle
open scoped Topology Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [FiniteDimensional ℝ E] in
private theorem mdifferentiableAt_tangentConstAt_of_mem
    (x₀ : M) (v : TangentSpace I x₀) {p : M}
    (hp : p ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    MDiffAt
      (T% (DifferentialGeometry.Integral.Connection.tangentConstAt (I := I) x₀ v :
        (q : M) -> TangentSpace I q)) p := by
  unfold DifferentialGeometry.Integral.Connection.tangentConstAt
  exact TensorLieDeriv.mdifferentiableAt_tangentConstInChart_of_mem
    (𝕜 := Real) (I := I) (x₀ := x₀) (p := p) v hp

omit [FiniteDimensional ℝ E] in
private theorem contMDiffAt_tangentConstAt_self_minTwo
    (x₀ : M) (v : TangentSpace I x₀) :
    ContMDiffAt I (I.prod 𝓘(Real, E)) (2 : ℕ∞)
      (T% (DifferentialGeometry.Integral.Connection.tangentConstAt (I := I) x₀ v :
        (p : M) -> TangentSpace I p)) x₀ := by
  let e := trivializationAt E (TangentSpace I) x₀
  have hx : x₀ ∈ e.baseSet :=
    mem_baseSet_trivializationAt E (TangentSpace I) x₀
  haveI : IsManifold I ((minSmoothness Real 2) + 1) M := by
    rw [minSmoothness_of_isRCLikeNormedField]
    norm_num
    exact (inferInstance : IsManifold I 3 M)
  haveI : IsManifold I (((2 : ℕ∞) : WithTop ℕ∞) + 1) M := by
    change IsManifold I (3 : WithTop ℕ∞) M
    exact (inferInstance : IsManifold I 3 M)
  have h_on :
      ContMDiffOn I (I.prod 𝓘(Real, E)) (2 : ℕ∞)
        (T% (DifferentialGeometry.Integral.Connection.tangentConstAt (I := I) x₀ v :
          (p : M) -> TangentSpace I p)) e.baseSet := by
    simpa [e, DifferentialGeometry.Integral.Connection.tangentConstAt] using
      (TensorLieDeriv.tangentConstInChart_contMDiffOn_baseSet
        (𝕜 := Real) (I := I) (M := M)
        (n := (2 : ℕ∞)) x₀ v)
  exact (h_on x₀ hx).contMDiffAt (e.open_baseSet.mem_nhds hx)

private theorem contMDiffAt_tangentConstAt_mlieBracket_self_one
    (x₀ : M) (v w : TangentSpace I x₀) :
    ContMDiffAt I (I.prod 𝓘(Real, E)) (1 : ℕ∞)
      (T% (VectorField.mlieBracket I
        (DifferentialGeometry.Integral.Connection.tangentConstAt (I := I) x₀ v)
        (DifferentialGeometry.Integral.Connection.tangentConstAt (I := I) x₀ w))) x₀ := by
  have hv : ContMDiffAt I (I.prod 𝓘(Real, E)) (2 : ℕ∞)
      (T% (DifferentialGeometry.Integral.Connection.tangentConstAt (I := I) x₀ v :
        (p : M) -> TangentSpace I p)) x₀ :=
    contMDiffAt_tangentConstAt_self_minTwo (I := I) x₀ v
  have hw : ContMDiffAt I (I.prod 𝓘(Real, E)) (2 : ℕ∞)
      (T% (DifferentialGeometry.Integral.Connection.tangentConstAt (I := I) x₀ w :
        (p : M) -> TangentSpace I p)) x₀ :=
    contMDiffAt_tangentConstAt_self_minTwo (I := I) x₀ w
  haveI : IsManifold I (minSmoothness Real 2) M := by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact (inferInstance : IsManifold I 2 M)
  haveI : IsManifold I (((2 : ℕ∞) : WithTop ℕ∞) + 1) M := by
    change IsManifold I (3 : WithTop ℕ∞) M
    exact (inferInstance : IsManifold I 3 M)
  exact
    ContMDiffAt.mlieBracket_vectorField (I := I) (m := (1 : ℕ∞))
      (n := (2 : ℕ∞)) hv hw (by
        rw [minSmoothness_of_isRCLikeNormedField]
        norm_num)

private theorem mdifferentiableAt_tangentConstAt_mlieBracket_self
    (x₀ : M) (v w : TangentSpace I x₀) :
    MDiffAt (T% (VectorField.mlieBracket I
      (DifferentialGeometry.Integral.Connection.tangentConstAt (I := I) x₀ v)
      (DifferentialGeometry.Integral.Connection.tangentConstAt (I := I) x₀ w))) x₀ :=
  (contMDiffAt_tangentConstAt_mlieBracket_self_one (I := I) x₀ v w).mdifferentiableAt
    (by norm_num : ((1 : ℕ∞) : WithTop ℕ∞) ≠ 0)

private theorem tangentConst_torsion_derivative_eq_add
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (1 : WithTop ℕ∞))
    (htf : DifferentialGeometry.Integral.Connection.IsTorsionFree (I := I) cov)
    (x : M) (A B C : TangentSpace I x) :
    (cov (fun p : M =>
        (cov (DifferentialGeometry.Integral.Connection.tangentConstAt (I := I) x B) p)
          (DifferentialGeometry.Integral.Connection.tangentConstAt (I := I) x A p)) x)
      (DifferentialGeometry.Integral.Connection.tangentConstAt (I := I) x C x) =
      (cov (fun p : M =>
          (cov (DifferentialGeometry.Integral.Connection.tangentConstAt (I := I) x A) p)
            (DifferentialGeometry.Integral.Connection.tangentConstAt (I := I) x B p)) x)
        (DifferentialGeometry.Integral.Connection.tangentConstAt (I := I) x C x) +
        (cov (VectorField.mlieBracket I
            (DifferentialGeometry.Integral.Connection.tangentConstAt (I := I) x A)
            (DifferentialGeometry.Integral.Connection.tangentConstAt (I := I) x B)) x)
          (DifferentialGeometry.Integral.Connection.tangentConstAt (I := I) x C x) := by
  let Ac : (p : M) -> TangentSpace I p := DifferentialGeometry.Integral.Connection.tangentConstAt (I := I) x A
  let Bc : (p : M) -> TangentSpace I p := DifferentialGeometry.Integral.Connection.tangentConstAt (I := I) x B
  let Cc : (p : M) -> TangentSpace I p := DifferentialGeometry.Integral.Connection.tangentConstAt (I := I) x C
  let ABc : (p : M) -> TangentSpace I p := fun p => (cov Bc p) (Ac p)
  let BAc : (p : M) -> TangentSpace I p := fun p => (cov Ac p) (Bc p)
  let BrAB : (p : M) -> TangentSpace I p := VectorField.mlieBracket I Ac Bc
  have hAB : MDiffAt (T% ABc) x := by
    simpa [ABc, Ac, Bc, DifferentialGeometry.Integral.Connection.tangentConstAt] using
      CovariantDerivative.tangentConst_cov_mdiffAt
        (𝕜 := Real) (I := I) cov hcov (x := x) (v := A) (w := B)
  have hBA : MDiffAt (T% BAc) x := by
    simpa [BAc, Ac, Bc, DifferentialGeometry.Integral.Connection.tangentConstAt] using
      CovariantDerivative.tangentConst_cov_mdiffAt
        (𝕜 := Real) (I := I) cov hcov (x := x) (v := B) (w := A)
  have hBr : MDiffAt (T% BrAB) x := by
    simpa [BrAB, Ac, Bc] using
      mdifferentiableAt_tangentConstAt_mlieBracket_self (I := I) x A B
  have hsum : MDiffAt (T% (BAc + BrAB)) x :=
    mdifferentiableAt_add_section hBA hBr
  have heq : ABc =ᶠ[𝓝 x] BAc + BrAB := by
    let e := trivializationAt E (TangentSpace I) x
    filter_upwards [e.open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt E (TangentSpace I) x)] with p hp
    have hAp : MDiffAt (T% Ac) p := by
      simpa [Ac] using mdifferentiableAt_tangentConstAt_of_mem (I := I) x A
        (by simpa [e] using hp)
    have hBp : MDiffAt (T% Bc) p := by
      simpa [Bc] using mdifferentiableAt_tangentConstAt_of_mem (I := I) x B
        (by simpa [e] using hp)
    have hzero :=
      congrArg
        (fun T : TangentSpace I p →L[Real] TangentSpace I p →L[Real] TangentSpace I p =>
          T (Ac p) (Bc p))
        (htf p)
    change cov.torsion p (Ac p) (Bc p) = 0 at hzero
    rw [cov.torsion_apply hAp hBp] at hzero
    have ht :
        (cov Bc p) (Ac p) - (cov Ac p) (Bc p) =
          VectorField.mlieBracket I Ac Bc p := by
      exact sub_eq_zero.mp hzero
    dsimp [ABc, BAc, BrAB] at ht ⊢
    rw [← ht]
    abel
  have hcongr : cov ABc x = cov (BAc + BrAB) x :=
    cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq hAB hsum (by simp) heq
  have happly :=
    congrArg (fun L : TangentSpace I x →L[Real] TangentSpace I x => L (Cc x)) hcongr
  rw [cov.isCovariantDerivativeOnUniv.add hBA hBr] at happly
  simpa [Ac, Bc, Cc, ABc, BAc, BrAB, Pi.add_apply] using happly

private theorem tangentConst_torsion_bracket_eq_add
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (htf : DifferentialGeometry.Integral.Connection.IsTorsionFree (I := I) cov)
    (x : M) (A B C : TangentSpace I x) :
    (cov (VectorField.mlieBracket I
        (DifferentialGeometry.Integral.Connection.tangentConstAt (I := I) x A)
        (DifferentialGeometry.Integral.Connection.tangentConstAt (I := I) x B)) x)
      (DifferentialGeometry.Integral.Connection.tangentConstAt (I := I) x C x) =
      (cov (DifferentialGeometry.Integral.Connection.tangentConstAt (I := I) x C) x)
        ((VectorField.mlieBracket I
          (DifferentialGeometry.Integral.Connection.tangentConstAt (I := I) x A)
          (DifferentialGeometry.Integral.Connection.tangentConstAt (I := I) x B)) x) +
        VectorField.mlieBracket I (DifferentialGeometry.Integral.Connection.tangentConstAt (I := I) x C)
          (VectorField.mlieBracket I
            (DifferentialGeometry.Integral.Connection.tangentConstAt (I := I) x A)
            (DifferentialGeometry.Integral.Connection.tangentConstAt (I := I) x B)) x := by
  let Ac : (p : M) -> TangentSpace I p := DifferentialGeometry.Integral.Connection.tangentConstAt (I := I) x A
  let Bc : (p : M) -> TangentSpace I p := DifferentialGeometry.Integral.Connection.tangentConstAt (I := I) x B
  let Cc : (p : M) -> TangentSpace I p := DifferentialGeometry.Integral.Connection.tangentConstAt (I := I) x C
  let BrAB : (p : M) -> TangentSpace I p := VectorField.mlieBracket I Ac Bc
  have hC : MDiffAt (T% Cc) x := by
    simpa [Cc] using mdifferentiableAt_tangentConstAt_of_mem (I := I) x C
      (mem_baseSet_trivializationAt E (TangentSpace I) x)
  have hBr : MDiffAt (T% BrAB) x := by
    simpa [BrAB, Ac, Bc] using
      mdifferentiableAt_tangentConstAt_mlieBracket_self (I := I) x A B
  have hzero :=
    congrArg
      (fun T : TangentSpace I x →L[Real] TangentSpace I x →L[Real] TangentSpace I x =>
        T (Cc x) (BrAB x))
      (htf x)
  change cov.torsion x (Cc x) (BrAB x) = 0 at hzero
  rw [cov.torsion_apply hC hBr] at hzero
  have ht :
      (cov BrAB x) (Cc x) - (cov Cc x) (BrAB x) =
        VectorField.mlieBracket I Cc BrAB x := by
    exact sub_eq_zero.mp hzero
  simpa [Ac, Bc, Cc, BrAB] using (sub_eq_iff_eq_add.mp ht).trans (by abel)

private theorem tangentConst_mlieBracket_jacobi_cyclic
    (x : M) (X Y Z : TangentSpace I x) :
    let Xc : (p : M) -> TangentSpace I p := DifferentialGeometry.Integral.Connection.tangentConstAt (I := I) x X
    let Yc : (p : M) -> TangentSpace I p := DifferentialGeometry.Integral.Connection.tangentConstAt (I := I) x Y
    let Zc : (p : M) -> TangentSpace I p := DifferentialGeometry.Integral.Connection.tangentConstAt (I := I) x Z
    let BrYZ : (p : M) -> TangentSpace I p := VectorField.mlieBracket I Yc Zc
    let BrZX : (p : M) -> TangentSpace I p := VectorField.mlieBracket I Zc Xc
    let BrXY : (p : M) -> TangentSpace I p := VectorField.mlieBracket I Xc Yc
    VectorField.mlieBracket I Xc BrYZ x +
      VectorField.mlieBracket I Yc BrZX x +
        VectorField.mlieBracket I Zc BrXY x = 0 := by
  let Xc : (p : M) -> TangentSpace I p := DifferentialGeometry.Integral.Connection.tangentConstAt (I := I) x X
  let Yc : (p : M) -> TangentSpace I p := DifferentialGeometry.Integral.Connection.tangentConstAt (I := I) x Y
  let Zc : (p : M) -> TangentSpace I p := DifferentialGeometry.Integral.Connection.tangentConstAt (I := I) x Z
  let BrYZ : (p : M) -> TangentSpace I p := VectorField.mlieBracket I Yc Zc
  let BrZX : (p : M) -> TangentSpace I p := VectorField.mlieBracket I Zc Xc
  let BrXY : (p : M) -> TangentSpace I p := VectorField.mlieBracket I Xc Yc
  haveI : IsManifold I (minSmoothness Real 3) M := by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact (inferInstance : IsManifold I 3 M)
  have h0 :
      VectorField.mlieBracket I Xc BrYZ x =
        VectorField.mlieBracket I BrXY Zc x +
          VectorField.mlieBracket I Yc (VectorField.mlieBracket I Xc Zc) x := by
    simpa [Xc, Yc, Zc, BrYZ, BrXY] using
      (VectorField.leibniz_identity_mlieBracket_apply (I := I)
        (U := Xc) (V := Yc) (W := Zc) (x := x)
        (by
          simpa [Xc, minSmoothness_of_isRCLikeNormedField] using
            contMDiffAt_tangentConstAt_self_minTwo (I := I) x X)
        (by
          simpa [Yc, minSmoothness_of_isRCLikeNormedField] using
            contMDiffAt_tangentConstAt_self_minTwo (I := I) x Y)
        (by
          simpa [Zc, minSmoothness_of_isRCLikeNormedField] using
            contMDiffAt_tangentConstAt_self_minTwo (I := I) x Z))
  rw [VectorField.mlieBracket_swap_apply (I := I) (V := BrXY) (W := Zc) (x := x)] at h0
  have hZX_mdiff : MDiffAt (T% BrZX) x := by
    simpa [BrZX, Zc, Xc] using
      mdifferentiableAt_tangentConstAt_mlieBracket_self (I := I) x Z X
  have hXZ : VectorField.mlieBracket I Xc Zc = (-1 : Real) • BrZX := by
    funext p
    simp [BrZX, VectorField.mlieBracket_swap_apply (I := I) (V := Xc) (W := Zc) (x := p)]
  rw [hXZ] at h0
  rw [VectorField.mlieBracket_const_smul_right (I := I) (c := (-1 : Real))
    (V := Yc) (W := BrZX) hZX_mdiff] at h0
  simp only [neg_smul, one_smul] at h0
  change
    VectorField.mlieBracket I Xc BrYZ x +
      VectorField.mlieBracket I Yc BrZX x +
        VectorField.mlieBracket I Zc BrXY x = 0
  rw [h0]
  abel

private theorem mlieBracket_jacobi_cyclic
    (X Y Z :
      ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (x : M) :
    let Xf : (p : M) -> TangentSpace I p := fun p => X p
    let Yf : (p : M) -> TangentSpace I p := fun p => Y p
    let Zf : (p : M) -> TangentSpace I p := fun p => Z p
    let BrYZ : (p : M) -> TangentSpace I p := VectorField.mlieBracket I Yf Zf
    let BrZX : (p : M) -> TangentSpace I p := VectorField.mlieBracket I Zf Xf
    let BrXY : (p : M) -> TangentSpace I p := VectorField.mlieBracket I Xf Yf
    VectorField.mlieBracket I Xf BrYZ x +
      VectorField.mlieBracket I Yf BrZX x +
        VectorField.mlieBracket I Zf BrXY x = 0 := by
  let Xf : (p : M) -> TangentSpace I p := fun p => X p
  let Yf : (p : M) -> TangentSpace I p := fun p => Y p
  let Zf : (p : M) -> TangentSpace I p := fun p => Z p
  let BrYZ : (p : M) -> TangentSpace I p := VectorField.mlieBracket I Yf Zf
  let BrZX : (p : M) -> TangentSpace I p := VectorField.mlieBracket I Zf Xf
  let BrXY : (p : M) -> TangentSpace I p := VectorField.mlieBracket I Xf Yf
  haveI : IsManifold I (minSmoothness Real 3) M := by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact (inferInstance : IsManifold I 3 M)
  haveI : IsManifold I (minSmoothness Real 2) M := by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact (inferInstance : IsManifold I 2 M)
  have h0 :
      VectorField.mlieBracket I Xf BrYZ x =
        VectorField.mlieBracket I BrXY Zf x +
          VectorField.mlieBracket I Yf (VectorField.mlieBracket I Xf Zf) x := by
    simpa [Xf, Yf, Zf, BrYZ, BrXY] using
      (VectorField.leibniz_identity_mlieBracket_apply (I := I)
        (U := Xf) (V := Yf) (W := Zf) (x := x)
        (X.contMDiff.contMDiffAt.of_le (by
          rw [minSmoothness_of_isRCLikeNormedField]
          exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤)))
        (Y.contMDiff.contMDiffAt.of_le (by
          rw [minSmoothness_of_isRCLikeNormedField]
          exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤)))
        (Z.contMDiff.contMDiffAt.of_le (by
          rw [minSmoothness_of_isRCLikeNormedField]
          exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))))
  rw [VectorField.mlieBracket_swap_apply (I := I) (V := BrXY) (W := Zf) (x := x)] at h0
  have hZX_mdiff : MDiffAt (T% BrZX) x := by
    haveI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
      simpa using (inferInstance : IsManifold I ∞ M)
    have hZX :
        ContMDiffAt I (I.prod 𝓘(Real, E)) (∞ : WithTop ℕ∞) (T% BrZX) x := by
      simpa [BrZX, Zf, Xf] using
        ContMDiffAt.mlieBracket_vectorField (I := I)
          (m := (⊤ : ℕ∞)) (n := (⊤ : ℕ∞))
          Z.contMDiff.contMDiffAt X.contMDiff.contMDiffAt
          (by simp [minSmoothness_of_isRCLikeNormedField])
    exact hZX.mdifferentiableAt (by simp)
  have hXZ : VectorField.mlieBracket I Xf Zf = (-1 : Real) • BrZX := by
    funext p
    simp [BrZX, VectorField.mlieBracket_swap_apply (I := I) (V := Xf) (W := Zf) (x := p)]
  rw [hXZ] at h0
  rw [VectorField.mlieBracket_const_smul_right (I := I) (c := (-1 : Real))
    (V := Yf) (W := BrZX) hZX_mdiff] at h0
  simp only [neg_smul, one_smul] at h0
  change
    VectorField.mlieBracket I Xf BrYZ x +
      VectorField.mlieBracket I Yf BrZX x +
        VectorField.mlieBracket I Zf BrXY x = 0
  rw [h0]
  abel



def vec5 {x : M} (A B C D F : TangentSpace I x) :
    Fin 5 -> TangentSpace I x :=
  fun i =>
    if i = 0 then A
    else if i = 1 then B
    else if i = 2 then C
    else if i = 3 then D
    else F



def FirstBianchiAt {x : M} (Rm04 : Tensor04At (I := I) (M := M) x) : Prop :=
  ∀ X Y Z W : TangentSpace I x,
    Rm04 (vec4 X Y Z W) + Rm04 (vec4 Y Z X W) + Rm04 (vec4 Z X Y W) = 0

omit [FiniteDimensional ℝ E] in
theorem first_bianchi {x : M} (Rm04 : Tensor04At (I := I) (M := M) x)
    (h : FirstBianchiAt (I := I) Rm04)
    (X Y Z W : TangentSpace I x) :
    Rm04 (vec4 X Y Z W) + Rm04 (vec4 Y Z X W) + Rm04 (vec4 Z X Y W) = 0 :=
  h X Y Z W


def FirstBianchiSection (Rm04 : Tensor04Section (I := I) (M := M)) : Prop :=
  ∀ x : M, FirstBianchiAt (I := I) (Rm04 x)

theorem first_bianchi_apply
    (Rm04 : Tensor04Section (I := I) (M := M))
    (h : FirstBianchiSection (I := I) Rm04)
    (x : M) (X Y Z W : TangentSpace I x) :
    Rm04 x (vec4 X Y Z W) + Rm04 x (vec4 Y Z X W) +
      Rm04 x (vec4 Z X Y W) = 0 :=
  h x X Y Z W







theorem connectionRiemannCurvatureField_tangentConst_first_bianchi_of_torsionFree
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (1 : WithTop ℕ∞))
    (htf : DifferentialGeometry.Integral.Connection.IsTorsionFree (I := I) cov)
    (x : M) (X Y Z : TangentSpace I x) :
    connectionRiemannCurvatureField (I := I) cov
        (DifferentialGeometry.Integral.Connection.tangentConstAt (I := I) x X)
        (DifferentialGeometry.Integral.Connection.tangentConstAt (I := I) x Y)
        (DifferentialGeometry.Integral.Connection.tangentConstAt (I := I) x Z) x +
      connectionRiemannCurvatureField (I := I) cov
        (DifferentialGeometry.Integral.Connection.tangentConstAt (I := I) x Y)
        (DifferentialGeometry.Integral.Connection.tangentConstAt (I := I) x Z)
        (DifferentialGeometry.Integral.Connection.tangentConstAt (I := I) x X) x +
      connectionRiemannCurvatureField (I := I) cov
        (DifferentialGeometry.Integral.Connection.tangentConstAt (I := I) x Z)
        (DifferentialGeometry.Integral.Connection.tangentConstAt (I := I) x X)
        (DifferentialGeometry.Integral.Connection.tangentConstAt (I := I) x Y) x = 0 := by
  unfold DifferentialGeometry.Integral.Connection.connectionRiemannCurvatureField
  rw [tangentConst_torsion_derivative_eq_add (I := I) cov hcov htf x Y Z X]
  rw [tangentConst_torsion_derivative_eq_add (I := I) cov hcov htf x Z X Y]
  rw [tangentConst_torsion_derivative_eq_add (I := I) cov hcov htf x X Y Z]
  rw [tangentConst_torsion_bracket_eq_add (I := I) cov htf x Y Z X]
  rw [tangentConst_torsion_bracket_eq_add (I := I) cov htf x Z X Y]
  rw [tangentConst_torsion_bracket_eq_add (I := I) cov htf x X Y Z]
  have hJac := tangentConst_mlieBracket_jacobi_cyclic (I := I) x X Y Z
  dsimp only at hJac
  abel_nf
  simpa [add_assoc] using hJac






def curvCovDerivOpAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X Y Z W :
      ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (x : M) : TangentSpace I x :=
  (cov (fun p : M =>
      connectionRiemannCurvatureField (I := I) cov
        (fun q : M => Y q) (fun q : M => Z q) (fun q : M => W q) p) x)
      (X x) -
    connectionRiemannCurvatureField (I := I) cov
      (fun p : M => (cov (fun q : M => Y q) p) (X p))
      (fun p : M => Z p) (fun p : M => W p) x -
    connectionRiemannCurvatureField (I := I) cov
      (fun p : M => Y p)
      (fun p : M => (cov (fun q : M => Z q) p) (X p))
      (fun p : M => W p) x -
    connectionRiemannCurvatureField (I := I) cov
      (fun p : M => Y p) (fun p : M => Z p)
      (fun p : M => (cov (fun q : M => W q) p) (X p)) x


def curvCommAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X Y Z W :
      ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (x : M) : TangentSpace I x :=
  (cov (fun p : M =>
      connectionRiemannCurvatureField (I := I) cov
        (fun q : M => Y q) (fun q : M => Z q) (fun q : M => W q) p) x)
      (X x) -
    connectionRiemannCurvatureField (I := I) cov
      (fun p : M => Y p) (fun p : M => Z p)
      (fun p : M => (cov (fun q : M => W q) p) (X p)) x



omit [FiniteDimensional ℝ E] in
theorem curvComm_eq_deriv
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X Y Z W :
      ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (x : M) :
    curvCommAt (I := I) cov X Y Z W x =
      curvCovDerivOpAt (I := I) cov X Y Z W x +
        connectionRiemannCurvatureField (I := I) cov
          (fun p : M => (cov (fun q : M => Y q) p) (X p))
          (fun p : M => Z p) (fun p : M => W p) x +
        connectionRiemannCurvatureField (I := I) cov
          (fun p : M => Y p)
          (fun p : M => (cov (fun q : M => Z q) p) (X p))
          (fun p : M => W p) x := by
  unfold curvCommAt curvCovDerivOpAt
  abel

private theorem curvBracket_mid
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (htf : DifferentialGeometry.Integral.Connection.IsTorsionFree (I := I) cov)
    (X Y Z W :
      ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (x : M) :
    connectionRiemannCurvatureField (I := I) cov
        (fun p : M => X p)
        (fun p : M =>
          VectorField.mlieBracket I (fun q : M => Y q) (fun q : M => Z q) p)
        (fun p : M => W p) x =
      connectionRiemannCurvatureField (I := I) cov
          (fun p : M => X p)
          (fun p : M => (cov (fun q : M => Z q) p) (Y p))
          (fun p : M => W p) x -
        connectionRiemannCurvatureField (I := I) cov
          (fun p : M => X p)
          (fun p : M => (cov (fun q : M => Y q) p) (Z p))
          (fun p : M => W p) x := by
  let Br : (p : M) -> TangentSpace I p :=
    fun p => VectorField.mlieBracket I (fun q : M => Y q) (fun q : M => Z q) p
  let DYZ : (p : M) -> TangentSpace I p :=
    fun p => (cov (fun q : M => Z q) p) (Y p)
  let DZY : (p : M) -> TangentSpace I p :=
    fun p => (cov (fun q : M => Y q) p) (Z p)
  let negDZY : (p : M) -> TangentSpace I p :=
    (fun _ : M => (-1 : Real)) • DZY
  let Ddiff : (p : M) -> TangentSpace I p := DYZ + negDZY
  have hYmd : MDiffAt (T% (fun p : M => Y p)) x :=
    Y.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hZmd : MDiffAt (T% (fun p : M => Z p)) x :=
    Z.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hDYZ : MDiffAt (T% DYZ) x := by
    simpa [DYZ] using
      DifferentialGeometry.Integral.Connection.CovariantDerivative.cov_smooth_apply_mdiffAt
        (I := I) cov hcov Y Z x
  have hDZY : MDiffAt (T% DZY) x := by
    simpa [DZY] using
      DifferentialGeometry.Integral.Connection.CovariantDerivative.cov_smooth_apply_mdiffAt
        (I := I) cov hcov Z Y x
  have hneg : MDiffAt (T% negDZY) x := by
    simpa [negDZY] using
      (mdifferentiableAt_const (I := I) (c := (-1 : Real))).smul_section hDZY
  have hDdiff : MDiffAt (T% Ddiff) x := by
    simpa [Ddiff] using mdifferentiableAt_add_section hDYZ hneg
  have hBr : MDiffAt (T% Br) x := by
    haveI : IsManifold I (minSmoothness Real 2) M := by
      rw [minSmoothness_of_isRCLikeNormedField]
      exact IsManifold.of_le (I := I) (M := M) (n := ∞)
        (by exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))
    haveI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
      simpa using (inferInstance : IsManifold I ∞ M)
    have hBrC :
        ContMDiffAt I (I.prod 𝓘(Real, E)) (∞ : WithTop ℕ∞) (T% Br) x := by
      simpa [Br] using
        ContMDiffAt.mlieBracket_vectorField (I := I)
          (m := (⊤ : ℕ∞)) (n := (⊤ : ℕ∞))
          Y.contMDiff.contMDiffAt Z.contMDiff.contMDiffAt
          (by simp [minSmoothness_of_isRCLikeNormedField])
    exact hBrC.mdifferentiableAt (by simp)
  have hBrVal : Br x = Ddiff x := by
    have hzero :=
      congrArg
        (fun T : TangentSpace I x →L[Real] TangentSpace I x →L[Real]
            TangentSpace I x => T (Y x) (Z x))
        (htf x)
    change cov.torsion x (Y x) (Z x) = 0 at hzero
    rw [cov.torsion_apply hYmd hZmd] at hzero
    have ht :
        DYZ x - DZY x = Br x := by
      simpa [DYZ, DZY, Br] using sub_eq_zero.mp hzero
    simpa [Br, DYZ, DZY, Ddiff, negDZY, Pi.add_apply, Pi.smul_apply,
      sub_eq_add_neg] using ht.symm
  let Φ : ((p : M) -> TangentSpace I p) -> TangentSpace I x :=
    fun U =>
      connectionRiemannCurvatureField (I := I) cov
        (fun p : M => X p) U (fun p : M => W p) x
  have hT :
      TensorialAt I E Φ x :=
    DifferentialGeometry.Integral.Connection.CovariantDerivative.connectionRiemannCurvatureField_tensorial_middle
      (I := I) cov hcov X W x
  calc
    connectionRiemannCurvatureField (I := I) cov
        (fun p : M => X p) Br (fun p : M => W p) x
        = connectionRiemannCurvatureField (I := I) cov
            (fun p : M => X p) Ddiff (fun p : M => W p) x := by
          exact TensorialAt.pointwise (I := I) (F := E) hT hBr hDdiff hBrVal
    _ = connectionRiemannCurvatureField (I := I) cov
          (fun p : M => X p) DYZ (fun p : M => W p) x +
        connectionRiemannCurvatureField (I := I) cov
          (fun p : M => X p) negDZY (fun p : M => W p) x := by
          exact hT.add hDYZ hneg
    _ = connectionRiemannCurvatureField (I := I) cov
          (fun p : M => X p) DYZ (fun p : M => W p) x -
        connectionRiemannCurvatureField (I := I) cov
          (fun p : M => X p) DZY (fun p : M => W p) x := by
          have hsmul' :
              connectionRiemannCurvatureField (I := I) cov
                  (fun p : M => X p) negDZY (fun p : M => W p) x =
                -connectionRiemannCurvatureField (I := I) cov
                  (fun p : M => X p) DZY (fun p : M => W p) x := by
            have hsmul := hT.smul (f := fun _ : M => (-1 : Real))
              (mdifferentiableAt_const (I := I) (c := (-1 : Real))) hDZY
            simpa [Φ, negDZY] using hsmul
          rw [hsmul']
          simp [sub_eq_add_neg]

private theorem curvTorsionCancel
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (htf : DifferentialGeometry.Integral.Connection.IsTorsionFree (I := I) cov)
    (X Y Z W :
      ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (x : M) :
    connectionRiemannCurvatureField (I := I) cov
        (fun p : M => (cov (fun q : M => Y q) p) (X p))
        (fun p : M => Z p) (fun p : M => W p) x +
      connectionRiemannCurvatureField (I := I) cov
        (fun p : M => Y p)
        (fun p : M => (cov (fun q : M => Z q) p) (X p))
        (fun p : M => W p) x +
      connectionRiemannCurvatureField (I := I) cov
        (fun p : M => (cov (fun q : M => Z q) p) (Y p))
        (fun p : M => X p) (fun p : M => W p) x +
      connectionRiemannCurvatureField (I := I) cov
        (fun p : M => Z p)
        (fun p : M => (cov (fun q : M => X q) p) (Y p))
        (fun p : M => W p) x +
      connectionRiemannCurvatureField (I := I) cov
        (fun p : M => (cov (fun q : M => X q) p) (Z p))
        (fun p : M => Y p) (fun p : M => W p) x +
      connectionRiemannCurvatureField (I := I) cov
        (fun p : M => X p)
        (fun p : M => (cov (fun q : M => Y q) p) (Z p))
        (fun p : M => W p) x +
      connectionRiemannCurvatureField (I := I) cov
        (fun p : M => X p)
        (fun p : M =>
          VectorField.mlieBracket I (fun q : M => Y q) (fun q : M => Z q) p)
        (fun p : M => W p) x +
      connectionRiemannCurvatureField (I := I) cov
        (fun p : M => Y p)
        (fun p : M =>
          VectorField.mlieBracket I (fun q : M => Z q) (fun q : M => X q) p)
        (fun p : M => W p) x +
      connectionRiemannCurvatureField (I := I) cov
        (fun p : M => Z p)
        (fun p : M =>
          VectorField.mlieBracket I (fun q : M => X q) (fun q : M => Y q) p)
        (fun p : M => W p) x = 0 := by
  rw [curvBracket_mid (I := I) cov hcov htf X Y Z W x]
  rw [curvBracket_mid (I := I) cov hcov htf Y Z X W x]
  rw [curvBracket_mid (I := I) cov hcov htf Z X Y W x]
  rw [DifferentialGeometry.Integral.Connection.connectionRiemannCurvatureField_swap
    (I := I) (cov := cov)
    (X := fun p : M => Z p)
    (Y := fun p : M => (cov (fun q : M => Y q) p) (X p))
    (Z := fun p : M => W p) (x := x)]
  rw [DifferentialGeometry.Integral.Connection.connectionRiemannCurvatureField_swap
    (I := I) (cov := cov)
    (X := fun p : M => X p)
    (Y := fun p : M => (cov (fun q : M => Z q) p) (Y p))
    (Z := fun p : M => W p) (x := x)]
  rw [DifferentialGeometry.Integral.Connection.connectionRiemannCurvatureField_swap
    (I := I) (cov := cov)
    (X := fun p : M => Y p)
    (Y := fun p : M => (cov (fun q : M => X q) p) (Z p))
    (Z := fun p : M => W p) (x := x)]
  abel

private theorem covCurvExpand
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (X Y Z W :
      ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (x : M) :
    (cov (fun p : M =>
        connectionRiemannCurvatureField (I := I) cov
          (fun q : M => Y q) (fun q : M => Z q) (fun q : M => W q) p) x)
        (X x) =
      (cov (fun p : M =>
          (cov (fun q : M => (cov (fun r : M => W r) q) (Z q)) p) (Y p)) x)
          (X x) -
        (cov (fun p : M =>
            (cov (fun q : M => (cov (fun r : M => W r) q) (Y q)) p) (Z p)) x)
            (X x) -
          (cov (fun p : M =>
              (cov (fun q : M => W q) p)
                (VectorField.mlieBracket I (fun q : M => Y q) (fun q : M => Z q) p)) x)
              (X x) := by
  let ZW : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
    ⟨fun p : M => (cov (fun q : M => W q) p) (Z p), by
      intro p
      exact DifferentialGeometry.Integral.Connection.CovariantDerivative.cov_smooth_apply_contMDiffAt
        (I := I) cov hcov Z W p⟩
  let YW : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
    ⟨fun p : M => (cov (fun q : M => W q) p) (Y p), by
      intro p
      exact DifferentialGeometry.Integral.Connection.CovariantDerivative.cov_smooth_apply_contMDiffAt
        (I := I) cov hcov Y W p⟩
  let BrYZ : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
    ⟨fun p : M => VectorField.mlieBracket I (fun q : M => Y q) (fun q : M => Z q) p, by
      intro p
      haveI : IsManifold I (minSmoothness Real 2) M := by
        rw [minSmoothness_of_isRCLikeNormedField]
        exact (inferInstance : IsManifold I 2 M)
      haveI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
        simpa using (inferInstance : IsManifold I ∞ M)
      exact
        ContMDiffAt.mlieBracket_vectorField (I := I)
          (m := (⊤ : ℕ∞)) (n := (⊤ : ℕ∞))
          Y.contMDiff.contMDiffAt Z.contMDiff.contMDiffAt
          (by simp [minSmoothness_of_isRCLikeNormedField])⟩
  let A : (p : M) -> TangentSpace I p :=
    fun p => (cov (fun q : M => ZW q) p) (Y p)
  let B : (p : M) -> TangentSpace I p :=
    fun p => (cov (fun q : M => YW q) p) (Z p)
  let C : (p : M) -> TangentSpace I p :=
    fun p => (cov (fun q : M => W q) p) (BrYZ p)
  let negB : (p : M) -> TangentSpace I p := -B
  let negC : (p : M) -> TangentSpace I p := -C
  have hA : MDiffAt (T% A) x := by
    simpa [A, ZW] using
      DifferentialGeometry.Integral.Connection.CovariantDerivative.cov_smooth_apply_mdiffAt
        (I := I) cov hcov Y ZW x
  have hB : MDiffAt (T% B) x := by
    simpa [B, YW] using
      DifferentialGeometry.Integral.Connection.CovariantDerivative.cov_smooth_apply_mdiffAt
        (I := I) cov hcov Z YW x
  have hC : MDiffAt (T% C) x := by
    simpa [C, BrYZ] using
      DifferentialGeometry.Integral.Connection.CovariantDerivative.cov_smooth_apply_mdiffAt
        (I := I) cov hcov BrYZ W x
  have hnegB : MDiffAt (T% negB) x := by
    simpa [negB] using mdifferentiableAt_neg_section hB
  have hnegC : MDiffAt (T% negC) x := by
    simpa [negC] using mdifferentiableAt_neg_section hC
  have hsum : MDiffAt (T% ((A + negB) + negC)) x := by
    exact mdifferentiableAt_add_section (mdifferentiableAt_add_section hA hnegB) hnegC
  have hR :
      MDiffAt
        (T% (fun p : M =>
          connectionRiemannCurvatureField (I := I) cov
            (fun q : M => Y q) (fun q : M => Z q) (fun q : M => W q) p)) x := by
    simpa [DifferentialGeometry.Integral.Connection.connectionRiemannCurvatureField,
      DifferentialGeometry.Integral.Connection.connectionRiemannCurvatureField, A, B, C, ZW, YW, BrYZ] using
      mdifferentiableAt_sub_section (mdifferentiableAt_sub_section hA hB) hC
  have heq :
      (fun p : M =>
          connectionRiemannCurvatureField (I := I) cov
            (fun q : M => Y q) (fun q : M => Z q) (fun q : M => W q) p)
        =ᶠ[𝓝 x] ((A + negB) + negC) := by
    refine Filter.Eventually.of_forall ?_
    intro p
    simp [DifferentialGeometry.Integral.Connection.connectionRiemannCurvatureField,
      DifferentialGeometry.Integral.Connection.connectionRiemannCurvatureField, A, B, C, negB, negC,
      ZW, YW, BrYZ, Pi.add_apply, sub_eq_add_neg, add_assoc]
  have hcongr :
      cov (fun p : M =>
          connectionRiemannCurvatureField (I := I) cov
            (fun q : M => Y q) (fun q : M => Z q) (fun q : M => W q) p) x =
        cov ((A + negB) + negC) x :=
    cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq hR hsum (by simp) heq
  have happly :=
    congrArg (fun L : TangentSpace I x →L[Real] TangentSpace I x => L (X x)) hcongr
  rw [cov.isCovariantDerivativeOnUniv.add
    (mdifferentiableAt_add_section hA hnegB) hnegC] at happly
  rw [cov.isCovariantDerivativeOnUniv.add hA hnegB] at happly
  have hnegB_cov :
      cov negB x = -cov B x := by
    simpa [negB] using
      cov.isCovariantDerivativeOnUniv.smul_const (-1 : Real) hB
  have hnegC_cov :
      cov negC x = -cov C x := by
    simpa [negC] using
      cov.isCovariantDerivativeOnUniv.smul_const (-1 : Real) hC
  rw [hnegB_cov, hnegC_cov] at happly
  simpa [A, B, C, negB, negC, ZW, YW, BrYZ, sub_eq_add_neg, add_assoc] using happly

private theorem curvJacobiAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (X Y Z W :
      ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (x : M) :
    curvCommAt (I := I) cov X Y Z W x +
      curvCommAt (I := I) cov Y Z X W x +
      curvCommAt (I := I) cov Z X Y W x +
      connectionRiemannCurvatureField (I := I) cov
        (fun p : M => X p)
        (fun p : M =>
          VectorField.mlieBracket I (fun q : M => Y q) (fun q : M => Z q) p)
        (fun p : M => W p) x +
      connectionRiemannCurvatureField (I := I) cov
        (fun p : M => Y p)
        (fun p : M =>
          VectorField.mlieBracket I (fun q : M => Z q) (fun q : M => X q) p)
        (fun p : M => W p) x +
      connectionRiemannCurvatureField (I := I) cov
        (fun p : M => Z p)
        (fun p : M =>
          VectorField.mlieBracket I (fun q : M => X q) (fun q : M => Y q) p)
        (fun p : M => W p) x = 0 := by







  have hJac := mlieBracket_jacobi_cyclic (I := I) X Y Z x
  have hJacCov :
      (cov (fun p : M => W p) x)
          (VectorField.mlieBracket I (fun p : M => X p)
            (fun p : M =>
              VectorField.mlieBracket I (fun q : M => Y q) (fun q : M => Z q) p) x) +
        (cov (fun p : M => W p) x)
          (VectorField.mlieBracket I (fun p : M => Y p)
            (fun p : M =>
              VectorField.mlieBracket I (fun q : M => Z q) (fun q : M => X q) p) x) +
          (cov (fun p : M => W p) x)
            (VectorField.mlieBracket I (fun p : M => Z p)
              (fun p : M =>
                VectorField.mlieBracket I (fun q : M => X q) (fun q : M => Y q) p) x) =
        0 := by
    have h :=
      congrArg (fun V : TangentSpace I x => (cov (fun p : M => W p) x) V) hJac
    dsimp only at h
    simpa using h
  unfold curvCommAt
  rw [covCurvExpand (I := I) cov hcov X Y Z W x]
  rw [covCurvExpand (I := I) cov hcov Y Z X W x]
  rw [covCurvExpand (I := I) cov hcov Z X Y W x]
  have hJacCovNeg := congrArg Neg.neg hJacCov
  simp only [DifferentialGeometry.Integral.Connection.connectionRiemannCurvatureField,
    DifferentialGeometry.Integral.Connection.connectionRiemannCurvatureField]
  abel_nf at hJacCovNeg ⊢
  exact hJacCovNeg







theorem curvSecondBianchi
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (htf : DifferentialGeometry.Integral.Connection.IsTorsionFree (I := I) cov)
    (X Y Z W :
      ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (x : M) :
    curvCovDerivOpAt (I := I) cov X Y Z W x +
      curvCovDerivOpAt (I := I) cov Y Z X W x +
        curvCovDerivOpAt (I := I) cov Z X Y W x = 0 := by
  let S : TangentSpace I x :=
    curvCovDerivOpAt (I := I) cov X Y Z W x +
      curvCovDerivOpAt (I := I) cov Y Z X W x +
        curvCovDerivOpAt (I := I) cov Z X Y W x
  let T : TangentSpace I x :=
    connectionRiemannCurvatureField (I := I) cov
        (fun p : M => (cov (fun q : M => Y q) p) (X p))
        (fun p : M => Z p) (fun p : M => W p) x +
      connectionRiemannCurvatureField (I := I) cov
        (fun p : M => Y p)
        (fun p : M => (cov (fun q : M => Z q) p) (X p))
        (fun p : M => W p) x +
      connectionRiemannCurvatureField (I := I) cov
        (fun p : M => (cov (fun q : M => Z q) p) (Y p))
        (fun p : M => X p) (fun p : M => W p) x +
      connectionRiemannCurvatureField (I := I) cov
        (fun p : M => Z p)
        (fun p : M => (cov (fun q : M => X q) p) (Y p))
        (fun p : M => W p) x +
      connectionRiemannCurvatureField (I := I) cov
        (fun p : M => (cov (fun q : M => X q) p) (Z p))
        (fun p : M => Y p) (fun p : M => W p) x +
      connectionRiemannCurvatureField (I := I) cov
        (fun p : M => X p)
        (fun p : M => (cov (fun q : M => Y q) p) (Z p))
        (fun p : M => W p) x +
      connectionRiemannCurvatureField (I := I) cov
        (fun p : M => X p)
        (fun p : M =>
          VectorField.mlieBracket I (fun q : M => Y q) (fun q : M => Z q) p)
        (fun p : M => W p) x +
      connectionRiemannCurvatureField (I := I) cov
        (fun p : M => Y p)
        (fun p : M =>
          VectorField.mlieBracket I (fun q : M => Z q) (fun q : M => X q) p)
        (fun p : M => W p) x +
      connectionRiemannCurvatureField (I := I) cov
        (fun p : M => Z p)
        (fun p : M =>
          VectorField.mlieBracket I (fun q : M => X q) (fun q : M => Y q) p)
        (fun p : M => W p) x
  change S = 0
  have hT : T = 0 := by
    simpa [T] using curvTorsionCancel (I := I) cov hcov htf X Y Z W x
  have hsum : S + T = 0 := by
    have hJ := curvJacobiAt (I := I) cov hcov X Y Z W x
    rw [curvComm_eq_deriv (I := I) cov X Y Z W x] at hJ
    rw [curvComm_eq_deriv (I := I) cov Y Z X W x] at hJ
    rw [curvComm_eq_deriv (I := I) cov Z X Y W x] at hJ
    dsimp [S, T]
    abel_nf at hJ ⊢
    exact hJ
  calc
    S = S + T := by rw [hT, add_zero]
    _ = 0 := hsum



def SecondBianchiAt {x : M}
    (nablaRm04 :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 5 x) :
    Prop :=
  ∀ A X Y Z W : TangentSpace I x,
    nablaRm04 (vec5 A X Y Z W) +
      nablaRm04 (vec5 X Y A Z W) +
        nablaRm04 (vec5 Y A X Z W) = 0

omit [FiniteDimensional ℝ E] in
theorem second_bianchi {x : M}
    (nablaRm04 :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 5 x)
    (h : SecondBianchiAt (I := I) nablaRm04)
    (A X Y Z W : TangentSpace I x) :
    nablaRm04 (vec5 A X Y Z W) +
      nablaRm04 (vec5 X Y A Z W) +
        nablaRm04 (vec5 Y A X Z W) = 0 :=
  h A X Y Z W


def SecondBianchiSection
    (nablaRm04 : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 5 x) :
    Prop :=
  ∀ x : M, SecondBianchiAt (I := I) (nablaRm04 x)

omit [FiniteDimensional ℝ E] in
theorem second_bianchi_apply
    (nablaRm04 : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 5 x)
    (h : SecondBianchiSection (I := I) nablaRm04)
    (x : M) (A X Y Z W : TangentSpace I x) :
    nablaRm04 x (vec5 A X Y Z W) +
      nablaRm04 x (vec5 X Y A Z W) +
        nablaRm04 x (vec5 Y A X Z W) = 0 :=
  h x A X Y Z W




def ContractedBianchiAt
    {Idx : Type*} [Fintype Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (nablaRic :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (dScalar :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x) :
    Prop :=
  ∀ X : TangentSpace I x,
    (∑ i : Idx, ∑ j : Idx,
      gInv i j * nablaRic (vec3 (basis i) (basis j) X)) =
        (1 / 2 : Real) * dScalar (fun _ : Fin 1 => X)

omit [FiniteDimensional ℝ E] in
theorem contracted_bianchi
    {Idx : Type*} [Fintype Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (nablaRic :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (dScalar :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (h : ContractedBianchiAt (I := I) basis gInv nablaRic dScalar)
    (X : TangentSpace I x) :
    (∑ i : Idx, ∑ j : Idx,
      gInv i j * nablaRic (vec3 (basis i) (basis j) X)) =
        (1 / 2 : Real) * dScalar (fun _ : Fin 1 => X) :=
  h X







omit [FiniteDimensional ℝ E] in
theorem dR_zero_nablaEin3
    {x : M}
    (g : SmoothMetric_gen I M)
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (gInv : Fin 3 -> Fin 3 -> Real)
    (hinv : MetricInverseInBasis_gen (I := I) g x basis gInv)
    (nablaRic :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (dScalar :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (hBianchi : ContractedBianchiAt (I := I) basis gInv nablaRic dScalar)
    (hEinNabla : ∀ A B C : TangentSpace I x,
      nablaRic (vec3 (I := I) A B C) =
        (1 / 3 : Real) * dScalar (fun _ : Fin 1 => A) * g.inner x B C) :
    ∀ X : TangentSpace I x, dScalar (fun _ : Fin 1 => X) = 0 := by
  classical
  intro X
  let α := cotangentToDual_gen (I := I) dScalar
  have hcoord :
      dScalar (fun _ : Fin 1 => X) =
        ∑ i : Fin 3, basis.repr X i *
          dScalar (fun _ : Fin 1 => basis i) := by
    calc
      dScalar (fun _ : Fin 1 => X) = α X := by
        simp [α, cotangentToDual_apply_gen]
      _ = α (∑ i : Fin 3, basis.repr X i • basis i) := by
        rw [basis.sum_repr]
      _ = ∑ i : Fin 3, basis.repr X i *
          dScalar (fun _ : Fin 1 => basis i) := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro i _hi
        simp [α, cotangentToDual_apply_gen, smul_eq_mul]
  have htrace :
      (∑ i : Fin 3, ∑ j : Fin 3,
        gInv i j * nablaRic (vec3 (I := I) (basis i) (basis j) X)) =
          (1 / 3 : Real) * dScalar (fun _ : Fin 1 => X) := by
    calc
      (∑ i : Fin 3, ∑ j : Fin 3,
        gInv i j * nablaRic (vec3 (I := I) (basis i) (basis j) X))
          = ∑ i : Fin 3, ∑ j : Fin 3,
              gInv i j *
                ((1 / 3 : Real) * dScalar (fun _ : Fin 1 => basis i) *
                  g.inner x (basis j) X) := by
            apply Finset.sum_congr rfl
            intro i _hi
            apply Finset.sum_congr rfl
            intro j _hj
            rw [hEinNabla]
      _ = (1 / 3 : Real) *
            (∑ i : Fin 3, ∑ j : Fin 3,
              gInv i j * g.inner x X (basis j) *
                dScalar (fun _ : Fin 1 => basis i)) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _hi
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _hj
            rw [g.symm x (basis j) X]
            ring
      _ = (1 / 3 : Real) * dScalar (fun _ : Fin 1 => X) := by
            rw [hcoord]
            congr 1
            apply Finset.sum_congr rfl
            intro i _hi
            rw [basis_repr_eq_sum_inv_inner (I := I) g x basis gInv hinv X i]
            rw [Finset.sum_mul]
  have hhalf :
      (1 / 2 : Real) * dScalar (fun _ : Fin 1 => X) =
        (1 / 3 : Real) * dScalar (fun _ : Fin 1 => X) := by
    rw [← hBianchi X, htrace]
  nlinarith



def ContrBianchiSec
    {Idx : Type*} [Fintype Idx]
    (basis : (x : M) -> Module.Basis Idx Real (TangentSpace I x))
    (gInv : (x : M) -> Idx -> Idx -> Real)
    (nablaRic : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (dScalar : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x) :
    Prop :=
  ∀ x : M,
    ContractedBianchiAt (I := I) (basis x) (gInv x) (nablaRic x) (dScalar x)

omit [FiniteDimensional ℝ E] in
theorem contrBianchi_apply
    {Idx : Type*} [Fintype Idx]
    (basis : (x : M) -> Module.Basis Idx Real (TangentSpace I x))
    (gInv : (x : M) -> Idx -> Idx -> Real)
    (nablaRic : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (dScalar : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (h : ContrBianchiSec (I := I) basis gInv nablaRic dScalar)
    (x : M) :
    ContractedBianchiAt (I := I) (basis x) (gInv x) (nablaRic x) (dScalar x) :=
  h x




def DScalarTraceAt
    {Idx : Type*} [Fintype Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (nablaRic :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (dScalar :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x) :
    Prop :=
  ∀ X : TangentSpace I x,
    dScalar (fun _ : Fin 1 => X) =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j * nablaRic (vec3 X (basis i) (basis j))


def DScalarTraceSec
    {Idx : Type*} [Fintype Idx]
    (basis : (x : M) -> Module.Basis Idx Real (TangentSpace I x))
    (gInv : (x : M) -> Idx -> Idx -> Real)
    (nablaRic : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (dScalar : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x) :
    Prop :=
  ∀ x : M, DScalarTraceAt (I := I) (basis x) (gInv x) (nablaRic x) (dScalar x)

omit [FiniteDimensional ℝ E] in
theorem dScalarTrace_apply
    {Idx : Type*} [Fintype Idx]
    (basis : (x : M) -> Module.Basis Idx Real (TangentSpace I x))
    (gInv : (x : M) -> Idx -> Idx -> Real)
    (nablaRic : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (dScalar : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (h : DScalarTraceSec (I := I) basis gInv nablaRic dScalar)
    (x : M) :
    DScalarTraceAt (I := I) (basis x) (gInv x) (nablaRic x) (dScalar x) :=
  h x



def NablaRicTraceAt
    {Idx : Type*} [Fintype Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (nablaRm04 :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 5 x)
    (nablaRic :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x) :
    Prop :=
  ∀ A B C : TangentSpace I x,
    nablaRic (vec3 A B C) =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j * nablaRm04 (vec5 A (basis i) B C (basis j))


def NablaRicTraceSec
    {Idx : Type*} [Fintype Idx]
    (basis : (x : M) -> Module.Basis Idx Real (TangentSpace I x))
    (gInv : (x : M) -> Idx -> Idx -> Real)
    (nablaRm04 : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 5 x)
    (nablaRic : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x) :
    Prop :=
  ∀ x : M, NablaRicTraceAt (I := I) (basis x) (gInv x) (nablaRm04 x) (nablaRic x)

omit [FiniteDimensional ℝ E] in
theorem nablaRicTrace_apply
    {Idx : Type*} [Fintype Idx]
    (basis : (x : M) -> Module.Basis Idx Real (TangentSpace I x))
    (gInv : (x : M) -> Idx -> Idx -> Real)
    (nablaRm04 : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 5 x)
    (nablaRic : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (h : NablaRicTraceSec (I := I) basis gInv nablaRm04 nablaRic)
    (x : M) :
    NablaRicTraceAt (I := I) (basis x) (gInv x) (nablaRm04 x) (nablaRic x) :=
  h x



def NablaRicSymmAt
    {x : M}
    (nablaRic :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x) :
    Prop :=
  ∀ A B C : TangentSpace I x,
    nablaRic (vec3 A B C) = nablaRic (vec3 A C B)


def NablaRicSymmSec
    (nablaRic : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x) :
    Prop :=
  ∀ x : M, NablaRicSymmAt (I := I) (nablaRic x)

omit [FiniteDimensional ℝ E] in
theorem nablaRicSymm_apply
    (nablaRic : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (h : NablaRicSymmSec (I := I) nablaRic) (x : M) :
    NablaRicSymmAt (I := I) (nablaRic x) :=
  h x





def NablaRmSymmAt
    {x : M}
    (nablaRm04 :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 5 x) :
    Prop :=
  (∀ A X Y Z W : TangentSpace I x,
      nablaRm04 (vec5 A X Y Z W) = -nablaRm04 (vec5 A X Y W Z)) ∧
    (∀ A X Y Z W : TangentSpace I x,
      nablaRm04 (vec5 A Y X Z W) = -nablaRm04 (vec5 A X Y Z W)) ∧
      ∀ A X Y Z W : TangentSpace I x,
        nablaRm04 (vec5 A X Y Z W) = nablaRm04 (vec5 A Z W X Y)


def NablaRmSymmSec
    (nablaRm04 : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 5 x) :
    Prop :=
  ∀ x : M, NablaRmSymmAt (I := I) (nablaRm04 x)

omit [FiniteDimensional ℝ E] in
theorem nablaRmSymm_apply
    (nablaRm04 : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 5 x)
    (h : NablaRmSymmSec (I := I) nablaRm04) (x : M) :
    NablaRmSymmAt (I := I) (nablaRm04 x) :=
  h x

private theorem trace_swap_symm
    {Idx : Type*} [Fintype Idx]
    (gInv : Idx -> Idx -> Real) (N : Idx -> Idx -> Real)
    (hInv : ∀ i j : Idx, gInv i j = gInv j i) :
    (∑ k : Idx, ∑ l : Idx, gInv k l * N l k) =
      ∑ k : Idx, ∑ l : Idx, gInv k l * N k l := by
  classical
  calc
    (∑ k : Idx, ∑ l : Idx, gInv k l * N l k) =
        ∑ l : Idx, ∑ k : Idx, gInv k l * N l k := by
          rw [Finset.sum_comm]
    _ = ∑ l : Idx, ∑ k : Idx, gInv l k * N l k := by
          refine Finset.sum_congr rfl fun l _ => ?_
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [hInv k l]
    _ = ∑ k : Idx, ∑ l : Idx, gInv k l * N k l := by
          rfl



omit [FiniteDimensional ℝ E] in
theorem contractTracesAt
    {Idx : Type*} [Fintype Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (nablaRic :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (dScalar :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (hBianchi : ContractedBianchiAt (I := I) basis gInv nablaRic dScalar)
    (hScalar : DScalarTraceAt (I := I) basis gInv nablaRic dScalar)
    (hNablaSymm : NablaRicSymmAt (I := I) nablaRic)
    (hInv : ∀ i j : Idx, gInv i j = gInv j i)
    (a : Idx) :
    (∑ k : Idx, ∑ l : Idx,
        gInv k l * nablaRic (vec3 (basis k) (basis a) (basis l))) =
      (1 / 2 : Real) *
        (∑ k : Idx, ∑ l : Idx,
          gInv k l * nablaRic (vec3 (basis a) (basis k) (basis l))) ∧
    (∑ k : Idx, ∑ l : Idx,
        gInv k l * nablaRic (vec3 (basis l) (basis k) (basis a))) =
      (1 / 2 : Real) *
        (∑ k : Idx, ∑ l : Idx,
          gInv k l * nablaRic (vec3 (basis a) (basis k) (basis l))) := by
  classical
  have hScalarA := hScalar (basis a)
  have hBianchiA := hBianchi (basis a)
  constructor
  · calc
      (∑ k : Idx, ∑ l : Idx,
          gInv k l * nablaRic (vec3 (basis k) (basis a) (basis l))) =
          ∑ k : Idx, ∑ l : Idx,
            gInv k l * nablaRic (vec3 (basis k) (basis l) (basis a)) := by
            refine Finset.sum_congr rfl fun k _ => ?_
            refine Finset.sum_congr rfl fun l _ => ?_
            rw [hNablaSymm (basis k) (basis a) (basis l)]
      _ = (1 / 2 : Real) * dScalar (fun _ : Fin 1 => basis a) := hBianchiA
      _ = (1 / 2 : Real) *
          (∑ k : Idx, ∑ l : Idx,
            gInv k l * nablaRic (vec3 (basis a) (basis k) (basis l))) := by
            rw [hScalarA]
  · calc
      (∑ k : Idx, ∑ l : Idx,
          gInv k l * nablaRic (vec3 (basis l) (basis k) (basis a))) =
          ∑ k : Idx, ∑ l : Idx,
            gInv k l * nablaRic (vec3 (basis k) (basis l) (basis a)) := by
            exact trace_swap_symm gInv
              (fun k l => nablaRic (vec3 (basis k) (basis l) (basis a))) hInv
      _ = (1 / 2 : Real) * dScalar (fun _ : Fin 1 => basis a) := hBianchiA
      _ = (1 / 2 : Real) *
          (∑ k : Idx, ∑ l : Idx,
            gInv k l * nablaRic (vec3 (basis a) (basis k) (basis l))) := by
            rw [hScalarA]




def ContractedBianchiOfSecondAt
    {Idx : Type*} [Fintype Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (nablaRm04 :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 5 x)
    (nablaRic :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (dScalar :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x) :
    Prop :=
  SecondBianchiAt (I := I) nablaRm04 ->
    ContractedBianchiAt (I := I) basis gInv nablaRic dScalar


def ContrOfSecondSec
    {Idx : Type*} [Fintype Idx]
    (basis : (x : M) -> Module.Basis Idx Real (TangentSpace I x))
    (gInv : (x : M) -> Idx -> Idx -> Real)
    (nablaRm04 : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 5 x)
    (nablaRic : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (dScalar : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x) :
    Prop :=
  ∀ x : M,
    ContractedBianchiOfSecondAt (I := I) (basis x) (gInv x)
      (nablaRm04 x) (nablaRic x) (dScalar x)

omit [FiniteDimensional ℝ E] in
theorem contrOfSecond_apply
    {Idx : Type*} [Fintype Idx]
    (basis : (x : M) -> Module.Basis Idx Real (TangentSpace I x))
    (gInv : (x : M) -> Idx -> Idx -> Real)
    (nablaRm04 : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 5 x)
    (nablaRic : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (dScalar : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (h : ContrOfSecondSec (I := I) basis gInv nablaRm04 nablaRic dScalar)
    (x : M) :
    ContractedBianchiOfSecondAt (I := I) (basis x) (gInv x)
      (nablaRm04 x) (nablaRic x) (dScalar x) :=
  h x

private theorem trace4_expand
    {Idx : Type*} [Fintype Idx]
    (gInv : Idx -> Idx -> Real)
    (F : Idx -> Idx -> Idx -> Idx -> Real) :
    (∑ i : Idx, ∑ j : Idx,
        gInv i j * (∑ k : Idx, ∑ l : Idx, gInv k l * F i j k l)) =
      ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        gInv i j * gInv k l * F i j k l := by
  classical
  simp [Finset.mul_sum, mul_assoc]

private theorem sum4_add3
    {Idx : Type*} [Fintype Idx]
    (F G H : Idx -> Idx -> Idx -> Idx -> Real) :
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx, F i j k l) +
        (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx, G i j k l) +
          (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx, H i j k l) =
      ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        (F i j k l + G i j k l + H i j k l) := by
  classical
  calc
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx, F i j k l) +
          (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx, G i j k l) +
        (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx, H i j k l)
        =
      (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          (F i j k l + G i j k l)) +
        (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx, H i j k l) := by
        simp [Finset.sum_add_distrib]
    _ =
      ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        ((F i j k l + G i j k l) + H i j k l) := by
        simp [Finset.sum_add_distrib]
    _ =
      ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        (F i j k l + G i j k l + H i j k l) := by
        rfl

private theorem sum4_swap34
    {Idx : Type*} [Fintype Idx]
    (gInv : Idx -> Idx -> Real)
    (F : Idx -> Idx -> Idx -> Idx -> Real)
    (hInv : ∀ i j : Idx, gInv i j = gInv j i) :
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        gInv i j * gInv k l * F i j l k) =
      ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        gInv i j * gInv k l * F i j k l := by
  classical
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  calc
    (∑ k : Idx, ∑ l : Idx, gInv i j * gInv k l * F i j l k) =
        gInv i j * (∑ k : Idx, ∑ l : Idx, gInv k l * F i j l k) := by
          simp [Finset.mul_sum, mul_assoc]
    _ = gInv i j * (∑ k : Idx, ∑ l : Idx, gInv k l * F i j k l) := by
          rw [trace_swap_symm gInv (fun k l => F i j k l) hInv]
    _ = ∑ k : Idx, ∑ l : Idx, gInv i j * gInv k l * F i j k l := by
          simp [Finset.mul_sum, mul_assoc]

private theorem sum4_lijk
    {Idx : Type*} [Fintype Idx]
    (gInv : Idx -> Idx -> Real)
    (F : Idx -> Idx -> Idx -> Idx -> Real)
    (hInv : ∀ i j : Idx, gInv i j = gInv j i) :
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        gInv i j * gInv k l * F l i j k) =
      ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        gInv i j * gInv k l * F i k l j := by
  classical
  rw [← Fintype.sum_prod_type']
  rw [← Fintype.sum_prod_type']
  rw [← Fintype.sum_prod_type']
  rw [show
      (∑ p : (((Idx × Idx) × Idx) × Idx),
        gInv p.1.1.1 p.1.1.2 * gInv p.1.2 p.2 *
          F p.2 p.1.1.1 p.1.1.2 p.1.2) =
      (∑ p : (((Idx × Idx) × Idx) × Idx),
        gInv p.1.1.1 p.1.1.2 * gInv p.1.2 p.2 *
          F p.1.1.1 p.1.2 p.2 p.1.1.2) by
        let e : (((Idx × Idx) × Idx) × Idx) ≃
            (((Idx × Idx) × Idx) × Idx) :=
          { toFun := fun p => (((p.2, p.1.2), p.1.1.1), p.1.1.2)
            invFun := fun p => (((p.1.2, p.2), p.1.1.2), p.1.1.1)
            left_inv := by
              intro p
              rcases p with ⟨⟨⟨i, j⟩, k⟩, l⟩
              rfl
            right_inv := by
              intro p
              rcases p with ⟨⟨⟨i, j⟩, k⟩, l⟩
              rfl }
        simpa [e] using
          (Fintype.sum_equiv e
            (fun p : (((Idx × Idx) × Idx) × Idx) =>
              gInv p.1.1.1 p.1.1.2 * gInv p.1.2 p.2 *
                F p.2 p.1.1.1 p.1.1.2 p.1.2)
            (fun p : (((Idx × Idx) × Idx) × Idx) =>
              gInv p.1.1.1 p.1.1.2 * gInv p.1.2 p.2 *
                F p.1.1.1 p.1.2 p.2 p.1.1.2)
            (by
              intro p
              rcases p with ⟨⟨⟨i, j⟩, k⟩, l⟩
              simp [e, hInv k l, mul_comm, mul_left_comm]))]
  rw [Fintype.sum_prod_type]
  rw [Fintype.sum_prod_type]
  rw [Fintype.sum_prod_type]

private theorem sum4_kjli
    {Idx : Type*} [Fintype Idx]
    (gInv : Idx -> Idx -> Real)
    (F : Idx -> Idx -> Idx -> Idx -> Real)
    (hInv : ∀ i j : Idx, gInv i j = gInv j i) :
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        gInv i j * gInv k l * F k j l i) =
      ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        gInv i j * gInv k l * F i k j l := by
  classical
  rw [← Fintype.sum_prod_type']
  rw [← Fintype.sum_prod_type']
  rw [← Fintype.sum_prod_type']
  rw [show
      (∑ p : (((Idx × Idx) × Idx) × Idx),
        gInv p.1.1.1 p.1.1.2 * gInv p.1.2 p.2 *
          F p.1.2 p.1.1.2 p.2 p.1.1.1) =
      (∑ p : (((Idx × Idx) × Idx) × Idx),
        gInv p.1.1.1 p.1.1.2 * gInv p.1.2 p.2 *
          F p.1.1.1 p.1.2 p.1.1.2 p.2) by
        let e : (((Idx × Idx) × Idx) × Idx) ≃
            (((Idx × Idx) × Idx) × Idx) :=
          { toFun := fun p => (((p.1.2, p.2), p.1.1.2), p.1.1.1)
            invFun := fun p => (((p.2, p.1.2), p.1.1.1), p.1.1.2)
            left_inv := by
              intro p
              rcases p with ⟨⟨⟨i, j⟩, k⟩, l⟩
              rfl
            right_inv := by
              intro p
              rcases p with ⟨⟨⟨i, j⟩, k⟩, l⟩
              rfl }
        simpa [e] using
          (Fintype.sum_equiv e
            (fun p : (((Idx × Idx) × Idx) × Idx) =>
              gInv p.1.1.1 p.1.1.2 * gInv p.1.2 p.2 *
                F p.1.2 p.1.1.2 p.2 p.1.1.1)
            (fun p : (((Idx × Idx) × Idx) × Idx) =>
              gInv p.1.1.1 p.1.1.2 * gInv p.1.2 p.2 *
                F p.1.1.1 p.1.2 p.1.1.2 p.2)
            (by
              intro p
              rcases p with ⟨⟨⟨i, j⟩, k⟩, l⟩
              simp [e, hInv i j, mul_comm, mul_left_comm]))]
  rw [Fintype.sum_prod_type]
  rw [Fintype.sum_prod_type]
  rw [Fintype.sum_prod_type]




omit [FiniteDimensional ℝ E] in
theorem contractSum
    {Idx : Type*} [Fintype Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (nablaRm04 :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 5 x)
    (hRmSymm : NablaRmSymmAt (I := I) nablaRm04)
    (hInv : ∀ i j : Idx, gInv i j = gInv j i)
    (hsecond : SecondBianchiAt (I := I) nablaRm04)
    (X : TangentSpace I x) :
    (∑ i : Idx, ∑ j : Idx,
        gInv i j *
          (∑ k : Idx, ∑ l : Idx,
            gInv k l *
              nablaRm04 (vec5 (basis i) (basis k) (basis j) X (basis l)))) =
      (1 / 2 : Real) *
        (∑ i : Idx, ∑ j : Idx,
          gInv i j *
            (∑ k : Idx, ∑ l : Idx,
              gInv k l *
                nablaRm04 (vec5 X (basis k) (basis i) (basis j) (basis l)))) := by
  classical
  rcases hRmSymm with ⟨hOut, hIn, hPair⟩
  rw [trace4_expand, trace4_expand]
  let L : Real :=
    ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      gInv i j * gInv k l *
        nablaRm04 (vec5 (basis i) (basis k) (basis j) X (basis l))
  let R : Real :=
    ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      gInv i j * gInv k l *
        nablaRm04 (vec5 X (basis k) (basis i) (basis j) (basis l))
  let A : Real :=
    ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      gInv i j * gInv k l *
        nablaRm04 (vec5 (basis k) (basis i) X (basis j) (basis l))
  let B : Real :=
    ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      gInv i j * gInv k l *
        nablaRm04 (vec5 (basis i) X (basis k) (basis j) (basis l))
  change L = (1 / 2 : Real) * R
  have hcyc : R + A + B = 0 := by
    dsimp [R, A, B]
    rw [sum4_add3]
    refine Finset.sum_eq_zero fun i _ => ?_
    refine Finset.sum_eq_zero fun j _ => ?_
    refine Finset.sum_eq_zero fun k _ => ?_
    refine Finset.sum_eq_zero fun l _ => ?_
    have h := hsecond X (basis k) (basis i) (basis j) (basis l)
    calc
      gInv i j * gInv k l *
            nablaRm04 (vec5 X (basis k) (basis i) (basis j) (basis l)) +
          gInv i j * gInv k l *
            nablaRm04 (vec5 (basis k) (basis i) X (basis j) (basis l)) +
            gInv i j * gInv k l *
              nablaRm04 (vec5 (basis i) X (basis k) (basis j) (basis l))
          =
        gInv i j * gInv k l *
          (nablaRm04 (vec5 X (basis k) (basis i) (basis j) (basis l)) +
            nablaRm04 (vec5 (basis k) (basis i) X (basis j) (basis l)) +
              nablaRm04 (vec5 (basis i) X (basis k) (basis j) (basis l))) := by
          ring_nf
      _ = 0 := by rw [h, mul_zero]
  have hA : A = -L := by
    dsimp [A, L]
    calc
      (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          gInv i j * gInv k l *
            nablaRm04 (vec5 (basis k) (basis i) X (basis j) (basis l))) =
        ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          gInv i j * gInv k l *
            (-nablaRm04 (vec5 (basis k) (basis j) (basis l) X (basis i))) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          refine Finset.sum_congr rfl fun j _ => ?_
          refine Finset.sum_congr rfl fun k _ => ?_
          refine Finset.sum_congr rfl fun l _ => ?_
          have h1 : nablaRm04 (vec5 (basis k) (basis i) X (basis j) (basis l)) =
              -nablaRm04 (vec5 (basis k) X (basis i) (basis j) (basis l)) := by
            have h := hIn (basis k) (basis i) X (basis j) (basis l)
            linarith
          have h2 := hPair (basis k) X (basis i) (basis j) (basis l)
          rw [h1, h2]
      _ = -(∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          gInv i j * gInv k l *
            nablaRm04 (vec5 (basis k) (basis j) (basis l) X (basis i))) := by
          simp [Finset.sum_neg_distrib]
      _ = -L := by
          rw [sum4_kjli gInv
            (fun a b c d =>
              nablaRm04 (vec5 (basis a) (basis b) (basis c) X (basis d)))
            hInv]
  have hB : B = -L := by
    dsimp [B, L]
    calc
      (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          gInv i j * gInv k l *
            nablaRm04 (vec5 (basis i) X (basis k) (basis j) (basis l))) =
        ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          gInv i j * gInv k l *
            (-nablaRm04 (vec5 (basis i) (basis l) (basis j) X (basis k))) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          refine Finset.sum_congr rfl fun j _ => ?_
          refine Finset.sum_congr rfl fun k _ => ?_
          refine Finset.sum_congr rfl fun l _ => ?_
          have h1 := hPair (basis i) X (basis k) (basis j) (basis l)
          have h2 : nablaRm04 (vec5 (basis i) (basis j) (basis l) X (basis k)) =
              -nablaRm04 (vec5 (basis i) (basis l) (basis j) X (basis k)) := by
            have h := hIn (basis i) (basis j) (basis l) X (basis k)
            linarith
          rw [h1, h2]
      _ = -(∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          gInv i j * gInv k l *
            nablaRm04 (vec5 (basis i) (basis l) (basis j) X (basis k))) := by
          simp [Finset.sum_neg_distrib]
      _ = -L := by
          rw [sum4_swap34 gInv
            (fun a b c d =>
              nablaRm04 (vec5 (basis a) (basis c) (basis b) X (basis d)))
            hInv]
  have hR : R = 2 * L := by
    linarith
  linarith



omit [FiniteDimensional ℝ E] in
theorem contractOfSecond
    {Idx : Type*} [Fintype Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (nablaRm04 :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 5 x)
    (nablaRic :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (dScalar :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (hRmSymm : NablaRmSymmAt (I := I) nablaRm04)
    (hRicTrace : NablaRicTraceAt (I := I) basis gInv nablaRm04 nablaRic)
    (hScalar : DScalarTraceAt (I := I) basis gInv nablaRic dScalar)
    (_hNablaSymm : NablaRicSymmAt (I := I) nablaRic)
    (hInv : ∀ i j : Idx, gInv i j = gInv j i) :
    ContractedBianchiOfSecondAt (I := I) basis gInv nablaRm04
      nablaRic dScalar := by
  intro hsecond X
  rw [hScalar X]
  calc
    (∑ i : Idx, ∑ j : Idx,
        gInv i j * nablaRic (vec3 (basis i) (basis j) X))
        =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j *
          (∑ k : Idx, ∑ l : Idx,
            gInv k l *
              nablaRm04 (vec5 (basis i) (basis k) (basis j) X (basis l))) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hRicTrace (basis i) (basis j) X]
    _ =
      (1 / 2 : Real) *
        (∑ i : Idx, ∑ j : Idx,
          gInv i j *
            (∑ k : Idx, ∑ l : Idx,
              gInv k l *
                nablaRm04 (vec5 X (basis k) (basis i) (basis j) (basis l)))) :=
        contractSum (I := I) basis gInv nablaRm04 hRmSymm hInv hsecond X
    _ =
      (1 / 2 : Real) *
        (∑ i : Idx, ∑ j : Idx,
          gInv i j * nablaRic (vec3 X (basis i) (basis j))) := by
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hRicTrace X (basis i) (basis j)]

omit [FiniteDimensional ℝ E] in
theorem contracted_bianchi_of_second
    {Idx : Type*} [Fintype Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (nablaRm04 :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 5 x)
    (nablaRic :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (dScalar :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (hcontract : ContractedBianchiOfSecondAt (I := I) basis gInv nablaRm04
      nablaRic dScalar)
    (hsecond : SecondBianchiAt (I := I) nablaRm04) :
    ContractedBianchiAt (I := I) basis gInv nablaRic dScalar :=
  hcontract hsecond

omit [FiniteDimensional ℝ E] in
theorem contrOfSecond_sec
    {Idx : Type*} [Fintype Idx]
    (basis : (x : M) -> Module.Basis Idx Real (TangentSpace I x))
    (gInv : (x : M) -> Idx -> Idx -> Real)
    (nablaRm04 : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 5 x)
    (nablaRic : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (dScalar : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (hcontract :
      ContrOfSecondSec (I := I) basis gInv nablaRm04 nablaRic dScalar)
    (hsecond : SecondBianchiSection (I := I) nablaRm04) :
    ContrBianchiSec (I := I) basis gInv nablaRic dScalar := by
  intro x
  exact contracted_bianchi_of_second (I := I) (basis x) (gInv x)
    (nablaRm04 x) (nablaRic x) (dScalar x) (hcontract x) (hsecond x)

end DifferentialGeometry.Integral.Connection
