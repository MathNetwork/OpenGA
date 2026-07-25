import DifferentialGeometry.Geometry.Curvature.Tensor
import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.HigherOrder
import DifferentialGeometry.Bundle.PartialMfderiv.Basic
import DifferentialGeometry.Bundle.PartialMfderiv.ModelMixed
import DifferentialGeometry.Bundle.PartialMfderiv.FixedBase
import DifferentialGeometry.Tensor.RSTensor.Derivation.NablaOnTensors
import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion











noncomputable section

set_option autoImplicit false
set_option linter.style.longLine false

open Bundle Tensor0SBundle DifferentialGeometry.Integral.Connection
open scoped BigOperators Manifold ContDiff Topology

namespace DifferentialGeometry.Integral.Connection

variable {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
variable {H : Type _} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type _} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

namespace CovariantDerivative

noncomputable def tangentConstAt (x : M) (v : TangentSpace I x) (p : M) :
    TangentSpace I p :=
  TensorLieDeriv.tangentConstInChart (𝕜 := Real) (I := I) x v p

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
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

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem mdifferentiableAt_tangentConstAt_self
    (x : M) (v : TangentSpace I x) :
    MDiffAt (T% (tangentConstAt (I := I) x v : (p : M) → TangentSpace I p)) x := by
  unfold tangentConstAt
  exact TensorLieDeriv.mdifferentiableAt_tangentConstInChart_of_mem
    (𝕜 := Real) (I := I) (x₀ := x) (p := x) v
    (mem_baseSet_trivializationAt E (TangentSpace I) x)

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
@[simp] theorem tangentConstAt_add (x : M) (v w : TangentSpace I x) :
    (tangentConstAt (I := I) x (v + w) : (p : M) → TangentSpace I p) =
      (tangentConstAt (I := I) x v : (p : M) → TangentSpace I p) +
        tangentConstAt (I := I) x w := by
  unfold tangentConstAt
  exact TensorLieDeriv.tangentConstInChart_add (𝕜 := Real) (I := I) x v w

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
@[simp] theorem tangentConstAt_smul (x : M) (a : Real) (v : TangentSpace I x) :
    (tangentConstAt (I := I) x (a • v) : (p : M) → TangentSpace I p) =
      a • (tangentConstAt (I := I) x v : (p : M) → TangentSpace I p) := by
  unfold tangentConstAt
  exact TensorLieDeriv.tangentConstInChart_smul (𝕜 := Real) (I := I) x a v

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem cov_tangentConst_apply_mdiffAt_self
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞)
    (x : M) (v w : TangentSpace I x) :
    MDiffAt
      (T% (fun p : M => (cov (tangentConstAt (I := I) x v) p)
        (tangentConstAt (I := I) x w p))) x := by
  unfold tangentConstAt
  let e := trivializationAt E (TangentSpace I) x
  have hx : x ∈ e.baseSet := by
    simp [e]
  haveI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
    simpa using (inferInstance : IsManifold I ∞ M)
  haveI : IsManifold I (((∞ : WithTop ℕ∞) + 1) + 1) M := by
    simpa using (inferInstance : IsManifold I ∞ M)
  have h_on :
      CMDiff[e.baseSet] ∞
        (T% (fun p : M =>
          (cov (TensorLieDeriv.tangentConstInChart (𝕜 := Real) (I := I) x v) p)
            (TensorLieDeriv.tangentConstInChart (𝕜 := Real) (I := I) x w p))) := by
    have hσ :
        CMDiff[e.baseSet] (∞ + 1)
          (T% (TensorLieDeriv.tangentConstInChart (𝕜 := Real) (I := I) x v :
            (p : M) → TangentSpace I p)) := by
      simpa [e] using
        (TensorLieDeriv.tangentConstInChart_contMDiffOn_baseSet
          (𝕜 := Real) (I := I) (M := M) (n := (∞ : WithTop ℕ∞) + 1) x v)
    have hcovσ :
        ContMDiffOn I (I.prod 𝓘(Real, E →L[Real] E)) ∞
          (fun p : M =>
            (⟨p, cov
              (TensorLieDeriv.tangentConstInChart (𝕜 := Real) (I := I) x v) p⟩ :
              TotalSpace (E →L[Real] E)
                (fun p : M => TangentSpace I p →L[Real] TangentSpace I p)))
          e.baseSet := by
      exact (hcov e.open_baseSet).contMDiff hσ
    have hX :
        CMDiff[e.baseSet] ∞
          (T% (TensorLieDeriv.tangentConstInChart (𝕜 := Real) (I := I) x w :
            (p : M) → TangentSpace I p)) := by
      simpa [e] using
        (TensorLieDeriv.tangentConstInChart_contMDiffOn_baseSet
          (𝕜 := Real) (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) x w)
    simpa [e] using hcovσ.clm_bundle_apply hX
  have h_at : CMDiffAt ∞
      (T% (fun p : M =>
        (cov (TensorLieDeriv.tangentConstInChart (𝕜 := Real) (I := I) x v) p)
          (TensorLieDeriv.tangentConstInChart (𝕜 := Real) (I := I) x w p))) x :=
    (h_on x hx).contMDiffAt (e.open_baseSet.mem_nhds hx)
  exact h_at.mdifferentiableAt (by simp)

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem cov_smooth_apply_mdiffAt
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (X Y : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (x : M) :
    MDiffAt (T% (fun p : M => (cov (fun q : M => Y q) p) (X p))) x := by
  let e := trivializationAt E (TangentSpace I) x
  have hx : x ∈ e.baseSet := by
    simp [e]
  haveI : IsManifold I (((1 : WithTop ℕ∞) + 1) + 1) M := by
    exact IsManifold.of_le (I := I) (M := M) (n := ∞)
      (by
        exact WithTop.coe_le_coe.2 (le_top : (3 : ℕ∞) ≤ (⊤ : ℕ∞)))
  have h_on :
      CMDiff[e.baseSet] (∞ : WithTop ℕ∞)
        (T% (fun p : M => (cov (fun q : M => Y q) p) (X p))) := by
    have hY :
        CMDiff[e.baseSet] ((∞ : WithTop ℕ∞) + 1)
          (T% (fun q : M => Y q)) := by
      simpa using Y.contMDiff.contMDiffOn
    have hcovY :
        ContMDiffOn I (I.prod 𝓘(Real, E →L[Real] E)) (∞ : WithTop ℕ∞)
          (fun p : M =>
            (⟨p, cov (fun q : M => Y q) p⟩ :
              TotalSpace (E →L[Real] E)
                (fun p : M => TangentSpace I p →L[Real] TangentSpace I p)))
          e.baseSet := by
      exact (hcov e.open_baseSet).contMDiff hY
    have hX :
        CMDiff[e.baseSet] (∞ : WithTop ℕ∞)
          (T% (fun p : M => X p)) := by
      exact X.contMDiff.contMDiffOn
    simpa [e] using hcovY.clm_bundle_apply hX
  have h_at : CMDiffAt (∞ : WithTop ℕ∞)
      (T% (fun p : M => (cov (fun q : M => Y q) p) (X p))) x :=
    (h_on x hx).contMDiffAt (e.open_baseSet.mem_nhds hx)
  exact h_at.mdifferentiableAt (by simp)

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem cov_smooth_apply_contMDiffAt
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (X Y : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (x : M) :
    ContMDiffAt I (I.prod 𝓘(Real, E)) (∞ : WithTop ℕ∞)
      (T% (fun p : M => (cov (fun q : M => Y q) p) (X p))) x := by
  let e := trivializationAt E (TangentSpace I) x
  have hx : x ∈ e.baseSet := by
    simp [e]
  haveI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
    simpa using (inferInstance : IsManifold I ∞ M)
  haveI : IsManifold I (((∞ : WithTop ℕ∞) + 1) + 1) M := by
    simpa using (inferInstance : IsManifold I ∞ M)
  have h_on :
      CMDiff[e.baseSet] (∞ : WithTop ℕ∞)
        (T% (fun p : M => (cov (fun q : M => Y q) p) (X p))) := by
    have hY :
        CMDiff[e.baseSet] ((∞ : WithTop ℕ∞) + 1)
          (T% (fun q : M => Y q)) := by
      simpa using Y.contMDiff.contMDiffOn
    have hcovY :
        ContMDiffOn I (I.prod 𝓘(Real, E →L[Real] E)) (∞ : WithTop ℕ∞)
          (fun p : M =>
            (⟨p, cov (fun q : M => Y q) p⟩ :
              TotalSpace (E →L[Real] E)
                (fun p : M => TangentSpace I p →L[Real] TangentSpace I p)))
          e.baseSet := by
      exact (hcov e.open_baseSet).contMDiff hY
    have hX :
        CMDiff[e.baseSet] (∞ : WithTop ℕ∞)
          (T% (fun p : M => X p)) := by
      exact X.contMDiff.contMDiffOn
    simpa [e] using hcovY.clm_bundle_apply hX
  exact (h_on x hx).contMDiffAt (e.open_baseSet.mem_nhds hx)

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem cov_smooth_apply_raw_mdiffAt
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    {X : (p : M) → TangentSpace I p}
    (Y : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    {x : M}
    (hX : MDiffAt (T% X) x) :
    MDiffAt (T% (fun p : M => (cov (fun q : M => Y q) p) (X p))) x := by
  let e := trivializationAt E (TangentSpace I) x
  have hx : x ∈ e.baseSet := by
    simp [e]
  haveI : IsManifold I (((1 : WithTop ℕ∞) + 1) + 1) M := by
    exact IsManifold.of_le (I := I) (M := M) (n := ∞)
      (by
        exact WithTop.coe_le_coe.2 (le_top : (3 : ℕ∞) ≤ (⊤ : ℕ∞)))
  have hY :
      CMDiff[e.baseSet] ((∞ : WithTop ℕ∞) + 1)
        (T% (fun q : M => Y q)) := by
    simpa using Y.contMDiff.contMDiffOn
  have hcovY_on :
      ContMDiffOn I (I.prod 𝓘(Real, E →L[Real] E)) (∞ : WithTop ℕ∞)
        (fun p : M =>
          (⟨p, cov (fun q : M => Y q) p⟩ :
            TotalSpace (E →L[Real] E)
              (fun p : M => TangentSpace I p →L[Real] TangentSpace I p)))
        e.baseSet := by
    exact (hcov e.open_baseSet).contMDiff hY
  have hcovY_at :
      ContMDiffAt I (I.prod 𝓘(Real, E →L[Real] E)) (∞ : WithTop ℕ∞)
        (fun p : M =>
          (⟨p, cov (fun q : M => Y q) p⟩ :
            TotalSpace (E →L[Real] E)
              (fun p : M => TangentSpace I p →L[Real] TangentSpace I p)))
        x :=
    (hcovY_on x hx).contMDiffAt (e.open_baseSet.mem_nhds hx)
  exact (hcovY_at.mdifferentiableAt (by simp)).clm_bundle_apply hX

omit [FiniteDimensional ℝ E] in
theorem curvField_contMDiffAt
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (X Y Z : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (x : M) :
    ContMDiffAt I (I.prod 𝓘(Real, E)) (∞ : WithTop ℕ∞)
      (T% (fun p : M =>
        connectionRiemannCurvatureField cov
          (fun q : M => X q) (fun q : M => Y q) (fun q : M => Z q) p)) x := by
  haveI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
    simpa using (inferInstance : IsManifold I ∞ M)
  haveI : IsManifold I (minSmoothness Real 2) M := by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact IsManifold.of_le (I := I) (M := M) (n := ∞)
      (by exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))
  let YZ : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _) :=
    ⟨fun p : M => (cov (fun q : M => Z q) p) (Y p), by
      intro p
      exact cov_smooth_apply_contMDiffAt (I := I) cov hcov Y Z p⟩
  let XZ : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _) :=
    ⟨fun p : M => (cov (fun q : M => Z q) p) (X p), by
      intro p
      exact cov_smooth_apply_contMDiffAt (I := I) cov hcov X Z p⟩
  let B : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _) :=
    ⟨fun p : M => VectorField.mlieBracket I (fun q : M => X q) (fun q : M => Y q) p, by
      intro p
      exact
        ContMDiffAt.mlieBracket_vectorField (I := I) (m := (⊤ : ℕ∞))
          (n := (⊤ : ℕ∞)) (X.contMDiff.contMDiffAt)
          (Y.contMDiff.contMDiffAt) (by
            simp [minSmoothness_of_isRCLikeNormedField])⟩
  have h1 :
      ContMDiffAt I (I.prod 𝓘(Real, E)) (∞ : WithTop ℕ∞)
        (T% (fun p : M => (cov (fun q : M => YZ q) p) (X p))) x :=
    cov_smooth_apply_contMDiffAt (I := I) cov hcov X YZ x
  have h2 :
      ContMDiffAt I (I.prod 𝓘(Real, E)) (∞ : WithTop ℕ∞)
        (T% (fun p : M => (cov (fun q : M => XZ q) p) (Y p))) x :=
    cov_smooth_apply_contMDiffAt (I := I) cov hcov Y XZ x
  have h3 :
      ContMDiffAt I (I.prod 𝓘(Real, E)) (∞ : WithTop ℕ∞)
        (T% (fun p : M => (cov (fun q : M => Z q) p) (B p))) x :=
    cov_smooth_apply_contMDiffAt (I := I) cov hcov B Z x
  simpa [DifferentialGeometry.Integral.Connection.connectionRiemannCurvatureField, YZ, XZ, B] using
    (h1.sub_section h2).sub_section h3

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem metric_inner_contMDiffAt
    (g : SmoothRiemannianMetric I M)
    {X Y : (p : M) → TangentSpace I p} {x : M} {n : WithTop ℕ∞}
    (hX : ContMDiffAt I (I.prod 𝓘(Real, E)) n (T% X) x)
    (hY : ContMDiffAt I (I.prod 𝓘(Real, E)) n (T% Y) x)
    (hn : n ≤ ∞) :
    ContMDiffAt I 𝓘(Real, Real) n
      (fun y : M => g.inner y (X y) (Y y)) x := by
  have hg :
      ContMDiffAt I
        (I.prod 𝓘(Real, E →L[Real] E →L[Real] Real)) n
        (fun y : M =>
          TotalSpace.mk' (E →L[Real] E →L[Real] Real)
            (E := fun y : M =>
              TangentSpace I y →L[Real] TangentSpace I y →L[Real] Real)
            y (g.inner y)) x :=
    (g.contMDiff.contMDiffAt).of_le hn
  have htotal :
      ContMDiffAt I (I.prod 𝓘(Real, Real)) n
        (fun y : M =>
          TotalSpace.mk' Real (E := Bundle.Trivial M Real) y
            (g.inner y (X y) (Y y))) x := by
    exact ContMDiffAt.clm_bundle_apply₂
      (F₁ := E) (F₂ := E) hg hX hY
  rw [contMDiffAt_totalSpace] at htotal
  exact htotal.2

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem cov_tangentConst_add_apply_eventuallyEq
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (x : M) (v₁ v₂ w : TangentSpace I x) :
    (fun p : M => (cov (tangentConstAt (I := I) x (v₁ + v₂)) p)
        (tangentConstAt (I := I) x w p))
      =ᶠ[𝓝 x]
    (fun p : M =>
      (cov (tangentConstAt (I := I) x v₁) p) (tangentConstAt (I := I) x w p) +
        (cov (tangentConstAt (I := I) x v₂) p) (tangentConstAt (I := I) x w p)) := by
  let e := trivializationAt E (TangentSpace I) x
  have hx : x ∈ e.baseSet := by
    simp [e]
  filter_upwards [e.open_baseSet.mem_nhds hx] with p hp
  have hv₁ : MDiffAt (T% (tangentConstAt (I := I) x v₁ : (p : M) → TangentSpace I p)) p := by
    unfold tangentConstAt
    exact TensorLieDeriv.mdifferentiableAt_tangentConstInChart_of_mem
      (𝕜 := Real) (I := I) (x₀ := x) (p := p) v₁ (by simpa [e] using hp)
  have hv₂ : MDiffAt (T% (tangentConstAt (I := I) x v₂ : (p : M) → TangentSpace I p)) p := by
    unfold tangentConstAt
    exact TensorLieDeriv.mdifferentiableAt_tangentConstInChart_of_mem
      (𝕜 := Real) (I := I) (x₀ := x) (p := p) v₂ (by simpa [e] using hp)
  rw [tangentConstAt_add]
  rw [cov.isCovariantDerivativeOnUniv.add hv₁ hv₂]
  simp

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem cov_tangentConst_smul_apply_eventuallyEq
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (x : M) (a : Real) (v w : TangentSpace I x) :
    (fun p : M => (cov (tangentConstAt (I := I) x (a • v)) p)
        (tangentConstAt (I := I) x w p))
      =ᶠ[𝓝 x]
    (fun p : M =>
      a • (cov (tangentConstAt (I := I) x v) p) (tangentConstAt (I := I) x w p)) := by
  let e := trivializationAt E (TangentSpace I) x
  have hx : x ∈ e.baseSet := by
    simp [e]
  filter_upwards [e.open_baseSet.mem_nhds hx] with p hp
  have hv : MDiffAt (T% (tangentConstAt (I := I) x v : (p : M) → TangentSpace I p)) p := by
    unfold tangentConstAt
    exact TensorLieDeriv.mdifferentiableAt_tangentConstInChart_of_mem
      (𝕜 := Real) (I := I) (x₀ := x) (p := p) v (by simpa [e] using hp)
  rw [tangentConstAt_smul]
  rw [cov.isCovariantDerivativeOnUniv.smul_const a hv]
  simp [Pi.smul_apply]






def riemannCurvatureAux
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X Y Z : (p : M) → TangentSpace I p) (x : M) : TangentSpace I x :=
  (cov (fun p => (cov Z p) (Y p)) x) (X x) -
    (cov (fun p => (cov Z p) (X p)) x) (Y x) -
      (cov Z x) (VectorField.mlieBracket I X Y x)

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
@[simp]
theorem riemannCurvatureAux_eq_connectionRiemannCurvatureField
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X Y Z : (p : M) → TangentSpace I p) (x : M) :
    riemannCurvatureAux cov X Y Z x =
      connectionRiemannCurvatureField cov X Y Z x := rfl



omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem connectionRiemannCurvatureField_congr_of_eventuallyEq
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (X X' Y Y' Z Z' :
      ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    {x : M}
    (hX : (fun p : M => X p) =ᶠ[𝓝 x] fun p : M => X' p)
    (hY : (fun p : M => Y p) =ᶠ[𝓝 x] fun p : M => Y' p)
    (hZ : (fun p : M => Z p) =ᶠ[𝓝 x] fun p : M => Z' p) :
    connectionRiemannCurvatureField cov
        (fun p : M => X p) (fun p : M => Y p) (fun p : M => Z p) x =
      connectionRiemannCurvatureField cov
        (fun p : M => X' p) (fun p : M => Y' p) (fun p : M => Z' p) x := by
  classical
  have hXx : X x = X' x := hX.self_of_nhds
  have hYx : Y x = Y' x := hY.self_of_nhds
  have hbr :
      VectorField.mlieBracket I (fun p : M => X p) (fun p : M => Y p) x =
        VectorField.mlieBracket I (fun p : M => X' p) (fun p : M => Y' p) x :=
    hX.mlieBracket_vectorField_eq (I := I) hY
  have hZ_at :
      cov (fun p : M => Z p) x = cov (fun p : M => Z' p) x := by
    exact cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
      (Z.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
      (Z'.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
      (by simp) hZ
  have hinnerY :
      (fun p : M => (cov (fun q : M => Z q) p) (Y p)) =ᶠ[𝓝 x]
        (fun p : M => (cov (fun q : M => Z' q) p) (Y' p)) := by
    rcases mem_nhds_iff.mp (hZ : {p : M | Z p = Z' p} ∈ 𝓝 x) with
      ⟨U, hUsub, hUopen, hxU⟩
    filter_upwards [hUopen.mem_nhds hxU, hY] with p hpU hYp
    have hZp :
        (fun q : M => Z q) =ᶠ[𝓝 p] fun q : M => Z' q := by
      exact Filter.eventuallyEq_of_mem (hUopen.mem_nhds hpU) fun q hq => hUsub hq
    have hcovp :
        cov (fun q : M => Z q) p = cov (fun q : M => Z' q) p := by
      exact cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
        (Z.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
        (Z'.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
        (by simp) hZp
    rw [hcovp, hYp]
  have hinnerX :
      (fun p : M => (cov (fun q : M => Z q) p) (X p)) =ᶠ[𝓝 x]
        (fun p : M => (cov (fun q : M => Z' q) p) (X' p)) := by
    rcases mem_nhds_iff.mp (hZ : {p : M | Z p = Z' p} ∈ 𝓝 x) with
      ⟨U, hUsub, hUopen, hxU⟩
    filter_upwards [hUopen.mem_nhds hxU, hX] with p hpU hXp
    have hZp :
        (fun q : M => Z q) =ᶠ[𝓝 p] fun q : M => Z' q := by
      exact Filter.eventuallyEq_of_mem (hUopen.mem_nhds hpU) fun q hq => hUsub hq
    have hcovp :
        cov (fun q : M => Z q) p = cov (fun q : M => Z' q) p := by
      exact cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
        (Z.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
        (Z'.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
        (by simp) hZp
    rw [hcovp, hXp]
  have hcovZY :
      cov (fun p : M => (cov (fun q : M => Z q) p) (Y p)) x =
        cov (fun p : M => (cov (fun q : M => Z' q) p) (Y' p)) x := by
    exact cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
      (cov_smooth_apply_mdiffAt (I := I) cov hcov Y Z x)
      (cov_smooth_apply_mdiffAt (I := I) cov hcov Y' Z' x)
      (by simp) hinnerY
  have hcovZX :
      cov (fun p : M => (cov (fun q : M => Z q) p) (X p)) x =
        cov (fun p : M => (cov (fun q : M => Z' q) p) (X' p)) x := by
    exact cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
      (cov_smooth_apply_mdiffAt (I := I) cov hcov X Z x)
      (cov_smooth_apply_mdiffAt (I := I) cov hcov X' Z' x)
      (by simp) hinnerX
  simp [DifferentialGeometry.Integral.Connection.connectionRiemannCurvatureField, hcovZY, hcovZX,
    hZ_at, hXx, hYx, hbr]

omit [FiniteDimensional ℝ E] in
theorem connectionRiemannCurvatureField_tensorial_left
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (Y Z : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (x : M) :
    TensorialAt I E
      (fun X : (p : M) → TangentSpace I p =>
        connectionRiemannCurvatureField cov X
          (fun p : M => Y p) (fun p : M => Z p) x) x where
  smul {f} {σ} hf hσ := by
    have hZY : MDiffAt
        (T% (fun p : M => (cov (fun q : M => Z q) p) (Y p))) x :=
      cov_smooth_apply_mdiffAt (I := I) cov hcov Y Z x
    have hZσ : MDiffAt
        (T% (fun p : M => (cov (fun q : M => Z q) p) (σ p))) x :=
      cov_smooth_apply_raw_mdiffAt (I := I) cov hcov Z hσ
    have hmid :
        (fun p : M => (cov (fun q : M => Z q) p) ((f • σ) p)) =
          f • (fun p : M => (cov (fun q : M => Z q) p) (σ p)) := by
      funext p
      simp [map_smul]
    simp only [DifferentialGeometry.Integral.Connection.connectionRiemannCurvatureField]
    rw [hmid]
    rw [cov.isCovariantDerivativeOnUniv.leibniz hZσ hf]
    rw [VectorField.mlieBracket_smul_left (I := I) hf hσ]
    simp [map_smul]
    module
  add {σ σ'} hσ hσ' := by
    have hZY : MDiffAt
        (T% (fun p : M => (cov (fun q : M => Z q) p) (Y p))) x :=
      cov_smooth_apply_mdiffAt (I := I) cov hcov Y Z x
    have hZσ : MDiffAt
        (T% (fun p : M => (cov (fun q : M => Z q) p) (σ p))) x :=
      cov_smooth_apply_raw_mdiffAt (I := I) cov hcov Z hσ
    have hZσ' : MDiffAt
        (T% (fun p : M => (cov (fun q : M => Z q) p) (σ' p))) x :=
      cov_smooth_apply_raw_mdiffAt (I := I) cov hcov Z hσ'
    have hmid :
        (fun p : M => (cov (fun q : M => Z q) p) ((σ + σ') p)) =
          (fun p : M => (cov (fun q : M => Z q) p) (σ p)) +
            (fun p : M => (cov (fun q : M => Z q) p) (σ' p)) := by
      funext p
      simp [map_add]
    simp only [DifferentialGeometry.Integral.Connection.connectionRiemannCurvatureField]
    rw [hmid]
    rw [cov.isCovariantDerivativeOnUniv.add hZσ hZσ']
    rw [VectorField.mlieBracket_add_left (I := I) hσ hσ']
    simp [map_add]
    module

omit [FiniteDimensional ℝ E] in
theorem connectionRiemannCurvatureField_tensorial_middle
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (X Z : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (x : M) :
    TensorialAt I E
      (fun Y : (p : M) → TangentSpace I p =>
        connectionRiemannCurvatureField cov
          (fun p : M => X p) Y (fun p : M => Z p) x) x where
  smul {f} {σ} hf hσ := by
    have hleft :=
      (connectionRiemannCurvatureField_tensorial_left
        (I := I) cov hcov X Z x).smul (f := f) (σ := σ) hf hσ
    rw [DifferentialGeometry.Integral.Connection.connectionRiemannCurvatureField_swap
      (I := I) (cov := cov) (X := f • σ) (Y := fun p : M => X p)
      (Z := fun p : M => Z p) (x := x)]
    rw [DifferentialGeometry.Integral.Connection.connectionRiemannCurvatureField_swap
      (I := I) (cov := cov) (X := σ) (Y := fun p : M => X p)
      (Z := fun p : M => Z p) (x := x)]
    rw [hleft]
    module
  add {σ σ'} hσ hσ' := by
    have hleft :=
      (connectionRiemannCurvatureField_tensorial_left
        (I := I) cov hcov X Z x).add (σ := σ) (σ' := σ') hσ hσ'
    rw [DifferentialGeometry.Integral.Connection.connectionRiemannCurvatureField_swap
      (I := I) (cov := cov) (X := σ + σ') (Y := fun p : M => X p)
      (Z := fun p : M => Z p) (x := x)]
    rw [DifferentialGeometry.Integral.Connection.connectionRiemannCurvatureField_swap
      (I := I) (cov := cov) (X := σ) (Y := fun p : M => X p)
      (Z := fun p : M => Z p) (x := x)]
    rw [DifferentialGeometry.Integral.Connection.connectionRiemannCurvatureField_swap
      (I := I) (cov := cov) (X := σ') (Y := fun p : M => X p)
      (Z := fun p : M => Z p) (x := x)]
    rw [hleft]
    module




theorem connectionRiemannCurvatureField_congr_first_two_point
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (X X' Y Y' Z :
      ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    {x : M}
    (hX : X x = X' x) (hY : Y x = Y' x) :
    connectionRiemannCurvatureField cov
        (fun p : M => X p) (fun p : M => Y p) (fun p : M => Z p) x =
      connectionRiemannCurvatureField cov
        (fun p : M => X' p) (fun p : M => Y' p) (fun p : M => Z p) x := by
  have hXmd : MDiffAt (T% (fun p : M => X p)) x :=
    X.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hX'md : MDiffAt (T% (fun p : M => X' p)) x :=
    X'.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hYmd : MDiffAt (T% (fun p : M => Y p)) x :=
    Y.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hY'md : MDiffAt (T% (fun p : M => Y' p)) x :=
    Y'.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  calc
    connectionRiemannCurvatureField cov
        (fun p : M => X p) (fun p : M => Y p) (fun p : M => Z p) x
        =
      connectionRiemannCurvatureField cov
        (fun p : M => X' p) (fun p : M => Y p) (fun p : M => Z p) x := by
        exact
          (connectionRiemannCurvatureField_tensorial_left
            (I := I) cov hcov Y Z x).pointwise hXmd hX'md hX
    _ =
      connectionRiemannCurvatureField cov
        (fun p : M => X' p) (fun p : M => Y' p) (fun p : M => Z p) x := by
        exact
          (connectionRiemannCurvatureField_tensorial_middle
            (I := I) cov hcov X' Z x).pointwise hYmd hY'md hY







private theorem connectionRiemannCurvatureField_smul_right_smooth
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (X Y Z :
      ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    {f : M → Real}
    (hf : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) f)
    (x : M) :
    connectionRiemannCurvatureField cov
        (fun p : M => X p) (fun p : M => Y p)
        (fun p : M => f p • Z p) x =
      f x • connectionRiemannCurvatureField cov
        (fun p : M => X p) (fun p : M => Y p)
        (fun p : M => Z p) x := by
  let Xf : M → Real := fun p => extDerivFun (I := I) f p (X p)
  let Yf : M → Real := fun p => extDerivFun (I := I) f p (Y p)
  let YZ : (p : M) → TangentSpace I p :=
    fun p => (cov (fun q : M => Z q) p) (Y p)
  let XZ : (p : M) → TangentSpace I p :=
    fun p => (cov (fun q : M => Z q) p) (X p)
  have hfmd : MDiffAt f x :=
    hf.contMDiffAt.mdifferentiableAt (by simp)
  have hXmd : MDiffAt (T% (fun p : M => X p)) x :=
    X.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hYmd : MDiffAt (T% (fun p : M => Y p)) x :=
    Y.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hZmd : MDiffAt (T% (fun p : M => Z p)) x :=
    Z.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hYZmd : MDiffAt (T% YZ) x :=
    cov_smooth_apply_mdiffAt (I := I) cov hcov Y Z x
  have hXZmd : MDiffAt (T% XZ) x :=
    cov_smooth_apply_mdiffAt (I := I) cov hcov X Z x
  have hYfmd : MDiffAt Yf x :=
    (DifferentialGeometry.extDerivFun_apply_contMDiffAt (I := I)
      hf.contMDiffAt Y).mdifferentiableAt (by simp)
  have hXfmd : MDiffAt Xf x :=
    (DifferentialGeometry.extDerivFun_apply_contMDiffAt (I := I)
      hf.contMDiffAt X).mdifferentiableAt (by simp)
  have hinnerY :
      (fun p : M => (cov (fun q : M => f q • Z q) p) (Y p)) =
        f • YZ + Yf • (fun p : M => Z p) := by
    funext p
    have hleib :
        cov (fun q : M => f q • Z q) p =
          f p • cov (fun q : M => Z q) p +
            (extDerivFun (I := I) f p).smulRight (Z p) := by
      simpa using
        (cov.isCovariantDerivativeOnUniv.leibniz
          (σ := fun q : M => Z q) (g := f) (x := p)
          (Z.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
          (hf.contMDiffAt.mdifferentiableAt (by simp)))
    simpa [YZ, Yf, Pi.add_apply, Pi.smul_apply] using
      congrArg (fun L : TangentSpace I p →L[Real] TangentSpace I p => L (Y p)) hleib
  have hinnerX :
      (fun p : M => (cov (fun q : M => f q • Z q) p) (X p)) =
        f • XZ + Xf • (fun p : M => Z p) := by
    funext p
    have hleib :
        cov (fun q : M => f q • Z q) p =
          f p • cov (fun q : M => Z q) p +
            (extDerivFun (I := I) f p).smulRight (Z p) := by
      simpa using
        (cov.isCovariantDerivativeOnUniv.leibniz
          (σ := fun q : M => Z q) (g := f) (x := p)
          (Z.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
          (hf.contMDiffAt.mdifferentiableAt (by simp)))
    simpa [XZ, Xf, Pi.add_apply, Pi.smul_apply] using
      congrArg (fun L : TangentSpace I p →L[Real] TangentSpace I p => L (X p)) hleib
  have hX2 :
      ContMDiffAt I (I.prod 𝓘(Real, E)) (minSmoothness Real 2)
        (T% (fun p : M => X p)) x := by
    exact X.contMDiff.contMDiffAt.of_le (by
      rw [minSmoothness_of_isRCLikeNormedField]
      exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ (⊤ : ℕ∞)))
  have hY2 :
      ContMDiffAt I (I.prod 𝓘(Real, E)) (minSmoothness Real 2)
        (T% (fun p : M => Y p)) x := by
    exact Y.contMDiff.contMDiffAt.of_le (by
      rw [minSmoothness_of_isRCLikeNormedField]
      exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ (⊤ : ℕ∞)))
  have hf2 : ContMDiffAt I 𝓘(Real, Real) (minSmoothness Real 2) f x := by
    exact hf.contMDiffAt.of_le (by
      rw [minSmoothness_of_isRCLikeNormedField]
      exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ (⊤ : ℕ∞)))
  have hscalar :
      extDerivFun (I := I) f x
          (VectorField.mlieBracket I (fun p : M => X p) (fun p : M => Y p) x) =
        extDerivFun (I := I) Yf x (X x) -
          extDerivFun (I := I) Xf x (Y x) := by
    simpa [vderiv, Xf, Yf] using
      (DifferentialGeometry.vderiv_mlieBracket
        (I := I) (fun p : M => X p) (fun p : M => Y p) f x hX2 hY2 hf2)
  simp only [DifferentialGeometry.Integral.Connection.connectionRiemannCurvatureField]
  rw [hinnerY, hinnerX]
  rw [cov.isCovariantDerivativeOnUniv.add
    ((hfmd.smul_section hYZmd)) (hYfmd.smul_section hZmd)]
  rw [cov.isCovariantDerivativeOnUniv.add
    ((hfmd.smul_section hXZmd)) (hXfmd.smul_section hZmd)]
  rw [cov.isCovariantDerivativeOnUniv.leibniz hYZmd hfmd]
  rw [cov.isCovariantDerivativeOnUniv.leibniz hZmd hYfmd]
  rw [cov.isCovariantDerivativeOnUniv.leibniz hXZmd hfmd]
  rw [cov.isCovariantDerivativeOnUniv.leibniz hZmd hXfmd]
  have hZsmul : (fun p : M => f p • Z p) = f • (fun p : M => Z p) := rfl
  rw [hZsmul]
  rw [cov.isCovariantDerivativeOnUniv.leibniz hZmd hfmd]
  simp [YZ, XZ, Xf, Yf, hscalar]
  module


omit [FiniteDimensional ℝ E] [CompleteSpace E] in
private theorem connectionRiemannCurvatureField_add_right_smooth
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (X Y Z Z' :
      ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (x : M) :
    connectionRiemannCurvatureField cov
        (fun p : M => X p) (fun p : M => Y p)
        (fun p : M => (Z + Z') p) x =
      connectionRiemannCurvatureField cov
          (fun p : M => X p) (fun p : M => Y p)
          (fun p : M => Z p) x +
        connectionRiemannCurvatureField cov
          (fun p : M => X p) (fun p : M => Y p)
          (fun p : M => Z' p) x := by
  let YZ : (p : M) → TangentSpace I p :=
    fun p => (cov (fun q : M => Z q) p) (Y p)
  let YZ' : (p : M) → TangentSpace I p :=
    fun p => (cov (fun q : M => Z' q) p) (Y p)
  let XZ : (p : M) → TangentSpace I p :=
    fun p => (cov (fun q : M => Z q) p) (X p)
  let XZ' : (p : M) → TangentSpace I p :=
    fun p => (cov (fun q : M => Z' q) p) (X p)
  have hZmd : MDiffAt (T% (fun p : M => Z p)) x :=
    Z.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hZ'md : MDiffAt (T% (fun p : M => Z' p)) x :=
    Z'.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hYZmd : MDiffAt (T% YZ) x :=
    cov_smooth_apply_mdiffAt (I := I) cov hcov Y Z x
  have hYZ'md : MDiffAt (T% YZ') x :=
    cov_smooth_apply_mdiffAt (I := I) cov hcov Y Z' x
  have hXZmd : MDiffAt (T% XZ) x :=
    cov_smooth_apply_mdiffAt (I := I) cov hcov X Z x
  have hXZ'md : MDiffAt (T% XZ') x :=
    cov_smooth_apply_mdiffAt (I := I) cov hcov X Z' x
  have hinnerY :
      (fun p : M => (cov (fun q : M => (Z + Z') q) p) (Y p)) = YZ + YZ' := by
    funext p
    have hleib :
        cov (fun q : M => (Z + Z') q) p =
          cov (fun q : M => Z q) p + cov (fun q : M => Z' q) p := by
      simpa using
        (cov.isCovariantDerivativeOnUniv.add
          (σ := fun q : M => Z q) (σ' := fun q : M => Z' q) (x := p)
          (Z.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
          (Z'.contMDiff.contMDiffAt.mdifferentiableAt (by simp)))
    simpa [YZ, YZ', Pi.add_apply] using
      congrArg (fun L : TangentSpace I p →L[Real] TangentSpace I p => L (Y p)) hleib
  have hinnerX :
      (fun p : M => (cov (fun q : M => (Z + Z') q) p) (X p)) = XZ + XZ' := by
    funext p
    have hleib :
        cov (fun q : M => (Z + Z') q) p =
          cov (fun q : M => Z q) p + cov (fun q : M => Z' q) p := by
      simpa using
        (cov.isCovariantDerivativeOnUniv.add
          (σ := fun q : M => Z q) (σ' := fun q : M => Z' q) (x := p)
          (Z.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
          (Z'.contMDiff.contMDiffAt.mdifferentiableAt (by simp)))
    simpa [XZ, XZ', Pi.add_apply] using
      congrArg (fun L : TangentSpace I p →L[Real] TangentSpace I p => L (X p)) hleib
  simp only [DifferentialGeometry.Integral.Connection.connectionRiemannCurvatureField]
  rw [hinnerY, hinnerX]
  rw [cov.isCovariantDerivativeOnUniv.add hYZmd hYZ'md]
  rw [cov.isCovariantDerivativeOnUniv.add hXZmd hXZ'md]
  have hZadd :
      (fun p : M => (Z + Z') p) =
        (fun p : M => Z p) + (fun p : M => Z' p) := rfl
  rw [hZadd]
  rw [cov.isCovariantDerivativeOnUniv.add hZmd hZ'md]
  simp [YZ, YZ', XZ, XZ']
  module

omit [CompleteSpace E] in
private theorem smooth_linear_tangentSection_pointwise
    [T2Space M]
    {x : M}
    (Φ :
      ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) →
        TangentSpace I x)
    (hadd : ∀ σ τ, Φ (σ + τ) = Φ σ + Φ τ)
    (hsmul : ∀ (f : C^∞⟮I, M; Real⟯) σ, Φ (f • σ) = f x • Φ σ)
    {σ τ : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _)}
    (hστ : σ x = τ x) :
    Φ σ = Φ τ := by
  classical
  have hzero : Φ 0 = 0 := by
    let z : C^∞⟮I, M; Real⟯ := ⟨fun _ => (0 : Real), contMDiff_const⟩
    have h := hsmul z (0 :
      ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    simpa [z] using h
  have hneg : ∀ σ, Φ (-σ) = -Φ σ := by
    intro σ
    let m : C^∞⟮I, M; Real⟯ := ⟨fun _ => (-1 : Real), contMDiff_const⟩
    have h := hsmul m σ
    have hm : m • σ = -σ := by
      ext y
      simp [m, ContMDiffSection.coe_smulContMDiffMap]
    rw [hm] at h
    simpa [m] using h
  have hsub : ∀ σ τ, Φ (σ - τ) = Φ σ - Φ τ := by
    intro σ τ
    calc
      Φ (σ - τ) = Φ (σ + -τ) := by rw [sub_eq_add_neg]
      _ = Φ σ + Φ (-τ) := hadd σ (-τ)
      _ = Φ σ - Φ τ := by rw [hneg τ, sub_eq_add_neg]
  have hsum :
      ∀ (s : Finset (Fin (Module.finrank Real E)))
        (u : Fin (Module.finrank Real E) →
          ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _)),
        Φ (∑ i ∈ s, u i) = ∑ i ∈ s, Φ (u i) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        intro u
        simp [hzero]
    | insert a s ha ih =>
        intro u
        simp [Finset.sum_insert ha, hadd, ih]
  have hlocal :
      ∀ (δ : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
        {U : Set M}, IsOpen U → x ∈ U → (∀ y ∈ U, δ y = 0) → Φ δ = 0 := by
    intro δ U hU hxU hδU
    obtain ⟨ψ, -, hψsupp⟩ :=
      (SmoothBumpFunction.nhds_basis_tsupport (I := I) x).mem_iff.mp
        (hU.mem_nhds hxU)
    let ψ' : C^∞⟮I, M; Real⟯ :=
      ⟨ψ, ψ.contMDiff⟩
    have hψδ : ψ' • δ = 0 := by
      ext y
      simp only [ContMDiffSection.coe_smulContMDiffMap,
        ContMDiffSection.coe_zero, Pi.zero_apply]
      by_cases hy : y ∈ Function.support (ψ : M → Real)
      · exact smul_eq_zero_of_right _ (hδU y (hψsupp (subset_closure hy)))
      · simp only [Function.mem_support, not_not] at hy
        exact smul_eq_zero_of_left hy _
    have h := hsmul ψ' δ
    rw [hψδ, hzero] at h
    simpa [ψ', ψ.eq_one] using h.symm
  suffices hvanish :
      ∀ δ : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _),
        δ x = 0 → Φ δ = 0 by
    have hδ := hvanish (σ - τ) (by
      simp only [ContMDiffSection.coe_sub, Pi.sub_apply, sub_eq_zero]
      exact hστ)
    rw [hsub σ τ] at hδ
    exact sub_eq_zero.mp hδ
  intro δ hδx
  let e := trivializationAt E (TangentSpace I) x
  let b := Module.finBasis Real E
  have he : x ∈ e.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) x
  have hframe := e.isLocalFrameOn_localFrame_baseSet I (∞ : WithTop ℕ∞) b
  obtain ⟨s', hs'⟩ := hframe.exists_contMDiffSection_eqOn_nhd e.open_baseSet he
  obtain ⟨χ, -, hχsupp⟩ :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := I) x).mem_iff.mp
      (e.open_baseSet.mem_nhds he)
  have hcoeff_smooth : ∀ i, ContMDiff I 𝓘(Real) (∞ : WithTop ℕ∞)
      (fun y : M => χ y • hframe.coeff i y (δ y)) := by
    intro i y
    by_cases hy : y ∈ tsupport (χ : M → Real)
    · have hcoeff :
          ContMDiffAt I 𝓘(Real) (∞ : WithTop ℕ∞)
            (fun y : M => e.localFrame_coeff I b i y (δ y)) y :=
        contMDiffAt_localFrame_coeff b (hχsupp hy) δ.contMDiff.contMDiffAt i
      have hχy : ContMDiffAt I 𝓘(Real) (∞ : WithTop ℕ∞) (χ : M → Real) y :=
        χ.contMDiff.contMDiffAt
      refine (hχy.smul hcoeff).congr_of_eventuallyEq ?_
      filter_upwards [((e.open_baseSet).mem_nhds (hχsupp hy))] with z hz
      have hbasis : e.basisAt b hz = hframe.toBasisAt hz := by
        ext j
        simp [IsLocalFrameOn.toBasisAt, Trivialization.localFrame,
          Trivialization.basisAt, hz]
      simp only [hframe.coeff_apply_of_mem hz,
        e.localFrame_coeff_apply_of_mem_baseSet b hz, hbasis]
    · have hχ_zero : ∀ᶠ z in 𝓝 y, (χ : M → Real) z = 0 := by
        apply Filter.Eventually.mono
          ((isClosed_tsupport (χ : M → Real)).isOpen_compl.mem_nhds hy)
        intro z hz
        exact (notMem_tsupport_iff_eventuallyEq.mp hz).self_of_nhds
      exact (contMDiffAt_const (c := (0 : Real))).congr_of_eventuallyEq
        (hχ_zero.mono fun z hz => by simp [hz])
  let u' : Fin (Module.finrank Real E) → C^∞⟮I, M; Real⟯ := fun i =>
    ⟨fun y : M => χ y • hframe.coeff i y (δ y), hcoeff_smooth i⟩
  have hu'_zero : ∀ i, (u' i) x = 0 := by
    intro i
    change χ x • hframe.coeff i x (δ x) = 0
    rw [χ.eq_one, one_smul, hδx, map_zero]
  have hδ_eq_near : ∀ᶠ y in 𝓝 x,
      δ y = ∑ i, (u' i) y • (s' i) y := by
    filter_upwards [hs', χ.eventuallyEq_one, e.open_baseSet.mem_nhds he] with
      y hs'y hχy hy
    change δ y = ∑ i, (χ y • hframe.coeff i y (δ y)) • (s' i) y
    simp only [show χ y = (1 : M → Real) y from hχy, Pi.one_apply, one_smul]
    conv_lhs => rw [hframe.coeff_sum_eq (⇑δ) hy]
    congr 1
    ext i
    rw [hs'y i]
  obtain ⟨U, hU_open, hxU, hU_vanish⟩ : ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
      ∀ y ∈ U, (δ - ∑ i, u' i • s' i) y = 0 := by
    obtain ⟨U, hU_nhds, hU⟩ := Filter.Eventually.exists_mem hδ_eq_near
    obtain ⟨U', hU'U, hU'_open, hxU'⟩ := mem_nhds_iff.mp hU_nhds
    refine ⟨U', hU'_open, hxU', ?_⟩
    intro y hy
    simp only [ContMDiffSection.coe_sub, Pi.sub_apply, sub_eq_zero,
      ContMDiffSection.finset_sum_apply_gen, ContMDiffSection.coe_smulContMDiffMap]
    exact hU y (hU'U hy)
  have hloc := hlocal (δ - ∑ i, u' i • s' i) hU_open hxU hU_vanish
  rw [hsub δ (∑ i, u' i • s' i)] at hloc
  have hsum_eval :
      Φ (∑ i, u' i • s' i) = ∑ i, Φ (u' i • s' i) :=
    hsum Finset.univ (fun i => u' i • s' i)
  rw [hsum_eval] at hloc
  simp_rw [hsmul] at hloc
  have hsum_zero : (∑ i, (u' i) x • Φ (s' i)) = 0 := by
    exact Finset.sum_eq_zero fun i _ => by rw [hu'_zero i, zero_smul]
  rw [hsum_zero, sub_zero] at hloc
  exact hloc








theorem connectionRiemannCurvatureField_congr_point
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    [T2Space M]
    (X X' Y Y' Z Z' :
      ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    {x : M}
    (hX : X x = X' x) (hY : Y x = Y' x) (hZ : Z x = Z' x) :
    connectionRiemannCurvatureField cov
        (fun p : M => X p) (fun p : M => Y p) (fun p : M => Z p) x =
      connectionRiemannCurvatureField cov
        (fun p : M => X' p) (fun p : M => Y' p) (fun p : M => Z' p) x := by
  calc
    connectionRiemannCurvatureField cov
        (fun p : M => X p) (fun p : M => Y p) (fun p : M => Z p) x
        =
      connectionRiemannCurvatureField cov
        (fun p : M => X' p) (fun p : M => Y' p) (fun p : M => Z p) x := by
        exact connectionRiemannCurvatureField_congr_first_two_point
          (I := I) cov hcov X X' Y Y' Z hX hY
    _ =
      connectionRiemannCurvatureField cov
        (fun p : M => X' p) (fun p : M => Y' p) (fun p : M => Z' p) x := by
        exact smooth_linear_tangentSection_pointwise
          (I := I) (x := x)
          (Φ := fun Zsec =>
            connectionRiemannCurvatureField cov
              (fun p : M => X' p) (fun p : M => Y' p)
              (fun p : M => Zsec p) x)
          (fun σ τ =>
            connectionRiemannCurvatureField_add_right_smooth
              (I := I) cov hcov X' Y' σ τ x)
          (fun f σ =>
            connectionRiemannCurvatureField_smul_right_smooth
              (I := I) cov hcov X' Y' σ (f := fun p : M => f p)
              f.contMDiff x)
          hZ


end CovariantDerivative

end DifferentialGeometry.Integral.Connection
