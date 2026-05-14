import OpenGALib.Riemannian.Connection.Koszul
import OpenGALib.Riemannian.Util.TangentHelpers
import OpenGALib.Riemannian.Util.MetricInnerSmoothness
/-!
# Half-Koszul cotangent functional

For `v : E` and `Y : SmoothVectorField I M`, the half-Koszul value
$\tfrac12 K(v_{\text{const}}, Y; w_{\text{const}})(y)$ on constant
lifts of `v, w` packages as a continuous linear functional
`koszulCotangentFunctional v Y y : E →L[ℝ] ℝ` — a cotangent vector at
`y` whose Riesz representative is $\nabla_v Y(y)$.

This module is Engineering scaffolding for `Connection.lean`'s Riesz
extraction (`koszulLinearFunctional_exists`, `koszulCovDeriv_exists`).
It depends on the Koszul algebraic identities from `Koszul.lean`
(`koszul_smul_right`, `koszul_add_right`) for the bilinearity of the
constant-lift functional, and on `TangentHelpers.lean` for the smoothness
componentwise-CLM lift.

The math layer (Riesz extraction → $\nabla_v Y$) lives in
`Connection.lean` and consumes `koszulCotangentFunctional_smoothAt` as
its smoothness witness for the cotangent section.
-/

open Bundle VectorField
open scoped ContDiff Manifold Topology

namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [IsLocallyConstantChartedSpace H M]
  [hm : HasMetric I M]

/-- **Mixed.** Half-Koszul scalar value $\tfrac12\,K(v_{\text{const}}, Y, w_{\text{const}})(y)$
on constant lifts of `v, w : E`. Math: the Koszul half-factor that
feeds Riesz uniqueness. Eng: paired with `koszulCotangentFunctional` to expose
the linearity in `w` to Riesz via a constant-lift wrapper. -/
noncomputable def koszulCotangentScalar
    (v : E) (Y : SmoothVectorField I M) (w : E) (y : M) : ℝ :=
  (1/2 : ℝ) * koszulFunctional (fun _ : M => v) Y.toFun (fun _ : M => w) y

/-- **Mixed.** Half-Koszul cotangent continuous linear map $w \mapsto \tfrac12\,K(v, Y; w)(y)$
as `E →L[ℝ] ℝ`. Math: bounded linear functional that Riesz represents
as $\nabla_v Y(y)$. Eng: linearity packaged via `koszul_smul_right` +
`koszul_add_right`. -/
noncomputable def koszulCotangentFunctional
    (v : E) (Y : SmoothVectorField I M) (y : M) : E →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w => koszulCotangentScalar v Y w y
      map_add' := by
        intro w₁ w₂
        unfold koszulCotangentScalar
        have hY_y : TangentSmoothAt Y.toFun y := Y.smoothAt y
        have h_const_w₁ : TangentSmoothAt (fun _ : M => w₁) y :=
          (SmoothVectorField.const (I := I) (M := M) w₁).smoothAt y
        have h_const_w₂ : TangentSmoothAt (fun _ : M => w₂) y :=
          (SmoothVectorField.const (I := I) (M := M) w₂).smoothAt y
        have h_YZ₁ : MDifferentiableAt I 𝓘(ℝ, ℝ)
            (fun y' : M => metricInner y' (Y.toFun y') ((fun _ : M => w₁) y')) y :=
          metricInner_mdifferentiableAt hY_y h_const_w₁
        have h_YZ₂ : MDifferentiableAt I 𝓘(ℝ, ℝ)
            (fun y' : M => metricInner y' (Y.toFun y') ((fun _ : M => w₂) y')) y :=
          metricInner_mdifferentiableAt hY_y h_const_w₂
        have h_Z₁X : MDifferentiableAt I 𝓘(ℝ, ℝ)
            (fun y' : M => metricInner y' ((fun _ : M => w₁) y') ((fun _ : M => v) y')) y :=
          metricInner_mdifferentiableAt h_const_w₁
            ((SmoothVectorField.const (I := I) (M := M) v).smoothAt y)
        have h_Z₂X : MDifferentiableAt I 𝓘(ℝ, ℝ)
            (fun y' : M => metricInner y' ((fun _ : M => w₂) y') ((fun _ : M => v) y')) y :=
          metricInner_mdifferentiableAt h_const_w₂
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
        have hY_y : TangentSmoothAt Y.toFun y := Y.smoothAt y
        have h_const_w : TangentSmoothAt (fun _ : M => w) y :=
          (SmoothVectorField.const (I := I) (M := M) w).smoothAt y
        have h_const_v : TangentSmoothAt (fun _ : M => v) y :=
          (SmoothVectorField.const (I := I) (M := M) v).smoothAt y
        have hf : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun _ : M => c) y :=
          mdifferentiableAt_const
        have h_YZ : MDifferentiableAt I 𝓘(ℝ, ℝ)
            (fun y' : M => metricInner y' (Y.toFun y') ((fun _ : M => w) y')) y :=
          metricInner_mdifferentiableAt hY_y h_const_w
        have h_ZX : MDifferentiableAt I 𝓘(ℝ, ℝ)
            (fun y' : M => metricInner y' ((fun _ : M => w) y') ((fun _ : M => v) y')) y :=
          metricInner_mdifferentiableAt h_const_w h_const_v
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

/-- **Eng.** `koszulCotangentFunctional` evaluated equals `koszulCotangentScalar`. -/
@[simp]
lemma koszulCotangentFunctional_apply (v : E) (Y : SmoothVectorField I M) (y : M) (w : E) :
    koszulCotangentFunctional v Y y w = koszulCotangentScalar v Y w y := rfl

omit [FiniteDimensional ℝ E] in
set_option backward.isDefEq.respectTransparency false in
/-- **Eng.** Scalar smoothness of `koszulCotangentScalar v Y w` in `y`,
decomposed across the 6 Koszul terms (3 directional-derivative + 3
mlieBracket-with-metric-inner). Used to lift `koszulCotangentFunctional` to a
smooth section. -/
private theorem koszulCotangentScalar_mdifferentiableAt
    (v : E) (Y : SmoothVectorField I M) (w : E) (x : M) :
    MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y : M => koszulCotangentScalar v Y w y) x := by
  classical
  -- Function-form smoothness witnesses, used downstream for `mfderiv_*_smoothAt`.
  have hY_E : ContMDiff I 𝓘(ℝ, E) ∞ Y.toFun := SmoothVectorField.contMDiff_E Y
  -- Bundle-section smoothness witnesses, used by `metricInner_contMDiff`.
  have hY_bundle : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun y => (⟨y, Y.toFun y⟩ : TangentBundle I M)) := Y.smooth
  have h_const_v_bundle : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun y => (⟨y, v⟩ : TangentBundle I M)) :=
    (SmoothVectorField.const (I := I) (M := M) v).smooth
  have h_const_w_bundle : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun y => (⟨y, w⟩ : TangentBundle I M)) :=
    (SmoothVectorField.const (I := I) (M := M) w).smooth
  -- Scalar functions for terms 1, 2, 3 via metricInner_contMDiff.
  have h_f_YW : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun y' : M => hm.metric.metricInner y' (Y.toFun y') w) :=
    metricInner_contMDiff hY_bundle h_const_w_bundle
  have h_f_WV : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun y' : M => hm.metric.metricInner y' w v) :=
    metricInner_contMDiff h_const_w_bundle h_const_v_bundle
  have h_f_VY : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun y' : M => hm.metric.metricInner y' v (Y.toFun y')) :=
    metricInner_contMDiff h_const_v_bundle hY_bundle
  -- TangentSmoothAt for the 3 const + Y bundle sections.
  have hY_y : TangentSmoothAt Y.toFun x := Y.smoothAt x
  have h_const_v_y : TangentSmoothAt (fun _ : M => v) x :=
    (SmoothVectorField.const (I := I) (M := M) v).smoothAt x
  have h_const_w_y : TangentSmoothAt (fun _ : M => w) x :=
    (SmoothVectorField.const (I := I) (M := M) w).smoothAt x
  -- TangentSmoothAt of mlieBracket sections (T4, T5, T6).
  have h_mlb_vY : TangentSmoothAt
      (mlieBracket I (fun _ : M => v) Y.toFun) x :=
    mlieBracket_tangentSmoothAt
      (SmoothVectorField.const (I := I) (M := M) v).smooth Y.smooth
  have h_mlb_Yw : TangentSmoothAt
      (mlieBracket I Y.toFun (fun _ : M => w)) x :=
    mlieBracket_tangentSmoothAt Y.smooth
      (SmoothVectorField.const (I := I) (M := M) w).smooth
  have h_mlb_vw : TangentSmoothAt
      (mlieBracket I (fun _ : M => v) (fun _ : M => w)) x :=
    mlieBracket_tangentSmoothAt
      (SmoothVectorField.const (I := I) (M := M) v).smooth
      (SmoothVectorField.const (I := I) (M := M) w).smooth
  -- 6 koszul terms in mfderiv form (skip directionalDeriv unfold step).
  have hT1 : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun y : M => mfderiv I 𝓘(ℝ, ℝ)
        (fun y' => metricInner y' (Y.toFun y') w) y v) x :=
    mfderiv_const_dir_smoothAt h_f_YW x v
  have hT2 : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun y : M => mfderiv I 𝓘(ℝ, ℝ)
        (fun y' => metricInner y' w v) y (Y.toFun y)) x :=
    mfderiv_smoothDir_smoothAt h_f_WV (hY_E.contMDiffAt)
  have hT3 : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun y : M => mfderiv I 𝓘(ℝ, ℝ)
        (fun y' => metricInner y' v (Y.toFun y')) y w) x :=
    mfderiv_const_dir_smoothAt h_f_VY x w
  have hT4 : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun y : M => metricInner y (mlieBracket I (fun _ : M => v) Y.toFun y) w) x :=
    metricInner_mdifferentiableAt h_mlb_vY h_const_w_y
  have hT5 : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun y : M => metricInner y (mlieBracket I Y.toFun (fun _ : M => w) y) v) x :=
    metricInner_mdifferentiableAt h_mlb_Yw h_const_v_y
  have hT6 : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun y : M => metricInner y
        (mlieBracket I (fun _ : M => v) (fun _ : M => w) y) (Y.toFun y)) x :=
    metricInner_mdifferentiableAt h_mlb_vw hY_y
  -- koszulCotangentScalar unfolds to (1/2) * koszulFunctional.
  -- koszulFunctional unfolds to T1 + T2 - T3 + T4 - T5 - T6 (directionalDeriv = mfderiv by def).
  unfold koszulCotangentScalar koszulFunctional directionalDeriv
  -- Goal: MDifferentiableAt of `fun y => (1/2) * (T1 + T2 - T3 + T4 - T5 - T6)` at x.
  exact ((((((hT1.add hT2).sub hT3).add hT4).sub hT5).sub hT6).const_smul (1/2 : ℝ))

/-- **Eng.** Smoothness of the koszul cotangent continuous linear map section as
`M → (E →L[ℝ] ℝ)`. Componentwise lift of `koszulCotangentScalar_mdifferentiableAt`
via `mdifferentiableAt_continuousLinearMap_of_components`. -/
theorem koszulCotangentFunctional_smoothAt
    (v : E) (Y : SmoothVectorField I M) (x : M) :
    MDifferentiableAt I 𝓘(ℝ, E →L[ℝ] ℝ)
      (fun y : M => koszulCotangentFunctional v Y y) x := by
  -- Componentwise lift: for each basis element b_i, the scalar
  -- (fun y => koszulCotangentFunctional v Y y (b_i)) = (fun y => koszulCotangentScalar v Y b_i y)
  -- is MDifferentiableAt at x by koszulCotangentScalar_mdifferentiableAt.
  -- Lift to continuous linear map via mdifferentiableAt_continuousLinearMap_of_components.
  set basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E := Module.finBasis ℝ E
  apply mdifferentiableAt_continuousLinearMap_of_components _ basis
  intro i
  show MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y : M => koszulCotangentFunctional v Y y (basis i)) x
  have h_eq : (fun y : M => koszulCotangentFunctional v Y y (basis i))
      = (fun y : M => koszulCotangentScalar v Y (basis i) y) := by
    funext y
    exact koszulCotangentFunctional_apply v Y y (basis i)
  rw [h_eq]
  exact koszulCotangentScalar_mdifferentiableAt v Y (basis i) x

end Riemannian
