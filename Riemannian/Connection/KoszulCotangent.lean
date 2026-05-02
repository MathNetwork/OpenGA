import Riemannian.Connection.Koszul
import Riemannian.Metric.RieszSmooth
import Riemannian.TangentBundle.MFDerivSmooth
import Riemannian.TangentBundle.SmoothVectorField

/-!
# Koszul cotangent CLM section

For `v : E` (chart-frame constant tangent direction) and `Y : SmoothVectorField I M`,
this file builds the **half-Koszul cotangent functional** as a smooth bundle CLM
section. Its Riesz extraction gives $\nabla_v Y$ (Levi-Civita along $v$).

**Used by**: `koszulCovDeriv_const_smoothAt` in `Riemannian/Connection/LeviCivita.lean`. -/

open Bundle VectorField OpenGALib
open scoped ContDiff Manifold Topology

namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [IsLocallyConstantChartedSpace H M]
  [RiemannianMetric I M]

/-- **Half-Koszul scalar value** $\tfrac12\,K(v_{\text{const}}, Y, w_{\text{const}})(y)$. -/
noncomputable def koszulCotangentScalar
    (v : E) (Y : SmoothVectorField I M) (w : E) (y : M) : ℝ :=
  (1/2 : ℝ) * koszulFunctional (fun _ : M => v) Y.toFun (fun _ : M => w) y

/-- **Half-Koszul cotangent CLM** $w \mapsto \tfrac12\,K(v, Y; w)(y)$ as
`E →L[ℝ] ℝ`. Linearity in `w` via `koszul_smul_right` + `koszul_add_right`. -/
noncomputable def koszulCotangentCLM
    (v : E) (Y : SmoothVectorField I M) (y : M) : E →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w => koszulCotangentScalar v Y w y
      map_add' := by
        intro w₁ w₂
        unfold koszulCotangentScalar
        have hY_y : OpenGALib.TangentSmoothAt Y.toFun y := Y.smoothAt y
        have h_const_w₁ : OpenGALib.TangentSmoothAt (fun _ : M => w₁) y :=
          (SmoothVectorField.const (I := I) (M := M) w₁).smoothAt y
        have h_const_w₂ : OpenGALib.TangentSmoothAt (fun _ : M => w₂) y :=
          (SmoothVectorField.const (I := I) (M := M) w₂).smoothAt y
        have h_YZ₁ : MDifferentiableAt I 𝓘(ℝ, ℝ)
            (fun y' : M => metricInner y' (Y.toFun y') ((fun _ : M => w₁) y')) y :=
          MDifferentiableAt.metricInner_smoothAt hY_y h_const_w₁
        have h_YZ₂ : MDifferentiableAt I 𝓘(ℝ, ℝ)
            (fun y' : M => metricInner y' (Y.toFun y') ((fun _ : M => w₂) y')) y :=
          MDifferentiableAt.metricInner_smoothAt hY_y h_const_w₂
        have h_Z₁X : MDifferentiableAt I 𝓘(ℝ, ℝ)
            (fun y' : M => metricInner y' ((fun _ : M => w₁) y') ((fun _ : M => v) y')) y :=
          MDifferentiableAt.metricInner_smoothAt h_const_w₁
            ((SmoothVectorField.const (I := I) (M := M) v).smoothAt y)
        have h_Z₂X : MDifferentiableAt I 𝓘(ℝ, ℝ)
            (fun y' : M => metricInner y' ((fun _ : M => w₂) y') ((fun _ : M => v) y')) y :=
          MDifferentiableAt.metricInner_smoothAt h_const_w₂
            ((SmoothVectorField.const (I := I) (M := M) v).smoothAt y)
        have h_add_factored :
            koszulFunctional (fun _ : M => v) Y.toFun (fun _ : M => w₁ + w₂) y
              = koszulFunctional (fun _ : M => v) Y.toFun (fun _ : M => w₁) y
                + koszulFunctional (fun _ : M => v) Y.toFun (fun _ : M => w₂) y := by
          have h_sum_eq : ((fun _ : M => w₁ + w₂) : ∀ z : M, TangentSpace I z)
              = (fun _ : M => w₁) + (fun _ : M => w₂) := by
            funext z; rfl
          rw [h_sum_eq]
          exact koszul_add_right (fun _ => v) Y.toFun (fun _ => w₁) (fun _ => w₂)
            y h_YZ₁ h_YZ₂ h_Z₁X h_Z₂X h_const_w₁ h_const_w₂
        show (1/2 : ℝ) * koszulFunctional (fun _ : M => v) Y.toFun
              (fun _ : M => w₁ + w₂) y
            = (1/2 : ℝ) * koszulFunctional (fun _ : M => v) Y.toFun (fun _ : M => w₁) y
              + (1/2 : ℝ) * koszulFunctional (fun _ : M => v) Y.toFun (fun _ : M => w₂) y
        rw [h_add_factored]
        ring
      map_smul' := by
        intro c w
        unfold koszulCotangentScalar
        -- Use koszul_smul_right with f = (const c).
        have hY_y : OpenGALib.TangentSmoothAt Y.toFun y := Y.smoothAt y
        have h_const_w : OpenGALib.TangentSmoothAt (fun _ : M => w) y :=
          (SmoothVectorField.const (I := I) (M := M) w).smoothAt y
        have h_const_v : OpenGALib.TangentSmoothAt (fun _ : M => v) y :=
          (SmoothVectorField.const (I := I) (M := M) v).smoothAt y
        have hf : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun _ : M => c) y :=
          mdifferentiableAt_const
        have h_YZ : MDifferentiableAt I 𝓘(ℝ, ℝ)
            (fun y' : M => metricInner y' (Y.toFun y') ((fun _ : M => w) y')) y :=
          MDifferentiableAt.metricInner_smoothAt hY_y h_const_w
        have h_ZX : MDifferentiableAt I 𝓘(ℝ, ℝ)
            (fun y' : M => metricInner y' ((fun _ : M => w) y') ((fun _ : M => v) y')) y :=
          MDifferentiableAt.metricInner_smoothAt h_const_w h_const_v
        have h_smul_factored :
            koszulFunctional (fun _ : M => v) Y.toFun (fun _ : M => c • w) y
              = c * koszulFunctional (fun _ : M => v) Y.toFun (fun _ : M => w) y := by
          have h_eq : (fun _ : M => c • w : ∀ z : M, TangentSpace I z)
              = fun y' : M => (fun _ : M => c) y' • (fun _ : M => w) y' := by
            funext z; rfl
          rw [h_eq]
          exact koszul_smul_right (fun _ => v) Y.toFun (fun _ => w)
            (fun _ : M => c) y hf h_YZ h_ZX h_const_w
        show (1/2 : ℝ) * koszulFunctional (fun _ : M => v) Y.toFun
              (fun _ : M => c • w) y
            = (RingHom.id ℝ) c • ((1/2 : ℝ) *
                koszulFunctional (fun _ : M => v) Y.toFun (fun _ : M => w) y)
        rw [h_smul_factored]
        simp
        ring }

@[simp]
lemma koszulCotangentCLM_apply (v : E) (Y : SmoothVectorField I M) (y : M) (w : E) :
    koszulCotangentCLM v Y y w = koszulCotangentScalar v Y w y := rfl

/-- **Smoothness of the koszul cotangent CLM section** as `M → (E →L[ℝ] ℝ)`.

This is the **single remaining PRE-PAPER sub-sorry** for the connection-level
smoothness clause. Closure plan (entirely mechanical, no paper-level math):

**Step A — scalar smoothness** of `koszulCotangentScalar v Y w` in `y` at every
`x`, for fixed `v, w : E` and `Y : SmoothVectorField`. Decomposes into 6
koszul-term smoothness checks via `unfold koszulFunctional`:

1. `directionalDeriv (fun y' => metricInner y' (Y y') w) y v` — chart-frame constant
   direction `v`, smooth scalar via `metricInner_smoothAt` with smooth `Y` and
   `const w`. Smoothness via `mfderiv_const_dir_smoothAt` (real proof in
   `Riemannian/TangentBundle/MFDerivSmooth.lean`).
2. `directionalDeriv (fun y' => metricInner y' w v) y (Y y)` — smoothly-varying
   direction `Y y` (via `set_option respectTransparency` + def-eq `T_yM = E`).
   Scalar smooth via `metricInner_smoothAt` with two const args.
   Smoothness via `mfderiv_smoothDir_smoothAt`.
3. `directionalDeriv (fun y' => metricInner y' v (Y y')) y w` — chart-frame constant
   direction `w`. Symmetric to (1). Via `mfderiv_const_dir_smoothAt`.
4. `metricInner y (mlieBracket I (const v) Y y) w` — smooth via Mathlib's
   `ContMDiffAt.mlieBracket_vectorField` + `metricInner_smoothAt`.
5. `metricInner y (mlieBracket I Y (const w) y) v` — symmetric to (4).
6. `metricInner y (mlieBracket I (const v) (const w) y) (Y y)` — both args
   chart-frame constants ⇒ `mlieBracket I (const v) (const w) y = 0` (since
   mfderivs of constants vanish under `IsLocallyConstantChartedSpace`).
   Hence the inner product is 0, smooth as the constant zero.

**Step B — CLM-valued lift**: componentwise smoothness from Step A lifted via
the framework's `contMDiffOn_clm_of_components` (Layer 2 smoothness lift,
`Riemannian/TangentBundle/Smoothness.lean`). For each basis element `b_i`,
`koszulCotangentCLM v Y y (b_i) = koszulCotangentScalar v Y (b_i) y` (by
`koszulCotangentCLM_apply`). Smoothness of each component scalar gives
CLM-valued smoothness in finite dim.

**Boundaryless prerequisite**: Step A uses `mfderiv_const_dir_smoothAt` and
`mfderiv_smoothDir_smoothAt` which require `[I.Boundaryless]`. The downstream
consumer chain (`koszulCovDeriv_const_smoothAt` →
`leviCivitaConnection_smoothAt_const_dir` → `Riemannian.Curvature` use sites)
will inherit this constraint at proof-time but not at signature-time. -/
theorem koszulCotangentCLM_smoothAt
    (v : E) (Y : SmoothVectorField I M) (x : M) :
    MDifferentiableAt I 𝓘(ℝ, E →L[ℝ] ℝ)
      (fun y : M => koszulCotangentCLM v Y y) x := by
  -- Single PRE-PAPER bridge sub-sorry; closure plan in docstring above.
  sorry

end Riemannian
