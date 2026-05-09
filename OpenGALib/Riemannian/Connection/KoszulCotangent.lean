import OpenGALib.Riemannian.Connection.Koszul
import OpenGALib.Riemannian.Metric.RieszSmooth
import OpenGALib.Riemannian.TangentBundle.MFDerivSmooth
import OpenGALib.Riemannian.TangentBundle.SmoothVectorField

/-!
# Koszul cotangent CLM section

For `v : E` (chart-frame constant tangent direction) and `Y : SmoothVectorField I M`,
this file builds the **half-Koszul cotangent functional** as a smooth bundle CLM
section. Its Riesz extraction gives $\nabla_v Y$ (Levi-Civita along $v$).

**Used by**: `koszulCovDeriv_const_smoothAt` in `OpenGALib/Riemannian/Connection/LeviCivita.lean`. -/

open Bundle VectorField OpenGALib
open scoped ContDiff Manifold Topology

namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [IsLocallyConstantChartedSpace H M]
  [g : RiemannianMetric I M]

/-! ## Helpers: flat-typed smoothness of `SmoothVectorField` and `metricInner` -/

omit [CompleteSpace E] [FiniteDimensional ℝ E] [RiemannianMetric I M] in
set_option backward.isDefEq.respectTransparency false in
/-- A `SmoothVectorField`'s underlying `Y.toFun : Π y : M, T_yM` viewed as
`M → E` (via `T_yM = E` def-eq) is globally `ContMDiff` under
`IsLocallyConstantChartedSpace`. -/
private theorem SmoothVectorField.contMDiff_E (Y : SmoothVectorField I M) :
    ContMDiff I 𝓘(ℝ, E) ∞ Y.toFun := by
  intro x
  set e := trivializationAt E (TangentSpace I) x with he_def
  -- Bundle-section smoothness gives chart-coord smoothness via Trivialization.contMDiffAt_iff.
  have h_he : (Bundle.TotalSpace.mk x (Y.toFun x) : TangentBundle I M) ∈ e.source := by
    rw [Bundle.Trivialization.mem_source]
    exact FiberBundle.mem_baseSet_trivializationAt' (F := E) x
  have h_iff := Bundle.Trivialization.contMDiffAt_iff (IM := I) (IB := I) (e := e)
    (f := fun y : M => (Bundle.TotalSpace.mk y (Y.toFun y) : TangentBundle I M))
    (n := ∞) h_he
  have h_chart_coord : ContMDiffAt I 𝓘(ℝ, E) ∞ (fun y : M => (e ⟨y, Y.toFun y⟩).2) x :=
    (h_iff.mp (Y.smooth x)).2
  -- On baseSet, (e ⟨y, V y⟩).2 = e.continuousLinearMapAt R y (V y).
  -- Under IsLocallyConstantChartedSpace, e.cLMA R y = id near x, so equals V y.
  apply h_chart_coord.congr_of_eventuallyEq
  have h_baseSet : e.baseSet ∈ 𝓝 x :=
    e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' x)
  have h_chart_eq : ∀ᶠ y in 𝓝 x, chartAt H y = chartAt H x :=
    chartAt_eventually_eq_of_locallyConstant x
  have h_chart_src : (chartAt H x).source ∈ 𝓝 x :=
    (chartAt H x).open_source.mem_nhds (mem_chart_source H x)
  filter_upwards [h_baseSet, h_chart_eq, h_chart_src] with y hy_base hy_eq hy_src
  show Y.toFun y = (e ⟨y, Y.toFun y⟩).2
  -- (e ⟨y, V y⟩).2 = e.continuousLinearMapAt R y (V y).
  rw [← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) e hy_base]
  -- e.continuousLinearMapAt R y = id near x via continuousLinearMapAtFlat = id (locally).
  show (Y.toFun y : E) = e.continuousLinearMapAt ℝ y (Y.toFun y)
  show (Y.toFun y : E) =
      TangentBundle.continuousLinearMapAtFlat (I := I) (M := M) x y (Y.toFun y)
  -- continuousLinearMapAtFlat x y = id near x (locally constant chart).
  have h_id : TangentBundle.continuousLinearMapAtFlat (I := I) (M := M) x y
      = ContinuousLinearMap.id ℝ E := by
    show (trivializationAt E (TangentSpace I) x).continuousLinearMapAt ℝ y
        = ContinuousLinearMap.id ℝ E
    rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core hy_src]
    have h_achart_eq : achart H y = achart H x := Subtype.ext hy_eq
    rw [h_achart_eq]
    ext v
    exact (tangentBundleCore I M).coordChange_self (achart H x) y
      (by simpa [tangentBundleCore_baseSet] using hy_src) v
  rw [h_id]
  rfl

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I ∞ M]
  [IsLocallyConstantChartedSpace H M] in
/-- **Smoothness of `g.metricTensor` applied to two `ContMDiff` flat-typed
sections**: `y ↦ g.metricTensor y (V y) (W y)` is `ContMDiff` whenever
`V, W : M → E` are. Uses `g.smoothMetric` + double `clm_apply`. -/
private theorem metricTensor_apply_contMDiff
    {V W : M → E} (hV : ContMDiff I 𝓘(ℝ, E) ∞ V) (hW : ContMDiff I 𝓘(ℝ, E) ∞ W) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun y : M => g.metricTensor y (V y) (W y)) := by
  intro x
  have h_metric : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞
      (fun y : M => g.metricTensor y) x :=
    (g.smoothMetric x)
  exact (h_metric.clm_apply (hV x)).clm_apply (hW x)

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I ∞ M]
  [IsLocallyConstantChartedSpace H M] in
set_option backward.isDefEq.respectTransparency false in
/-- **Smoothness of `metricInner` for two `ContMDiff` flat-typed sections**.
Bridges `metricTensor_apply_contMDiff` to the framework `metricInner` via
`metricInner_apply` (def-eq + `set_option`). -/
private theorem metricInner_contMDiff
    {V W : M → E} (hV : ContMDiff I 𝓘(ℝ, E) ∞ V) (hW : ContMDiff I 𝓘(ℝ, E) ∞ W) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun y : M => metricInner (g := g) y (V y) (W y)) := by
  have h_eq : (fun y : M => metricInner (g := g) y (V y) (W y))
      = (fun y : M => g.metricTensor y (V y) (W y)) := by
    funext y
    exact metricInner_apply (g := g) y (V y) (W y)
  rw [h_eq]
  exact metricTensor_apply_contMDiff hV hW

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I ∞ M]
  [IsLocallyConstantChartedSpace H M] [g : RiemannianMetric I M] in
/-- **MDifferentiableAt componentwise lift to CLM-valued**: if each component
`(fun y => T y (basis i)) : M → F₂` is `MDifferentiableAt` at `x`, then the
CLM-valued section `T : M → (F₁ →L[ℝ] F₂)` is `MDifferentiableAt` at `x`.

Proof: decompose `T y = ∑ i, (basis.coord i).toCLM.smulRight (T y (basis i))`,
each summand `MDifferentiableAt` via `clm_apply` of constant CLM `smulRightL`
with smooth scalar component, sum via `MDifferentiableAt.add`. -/
private theorem mdifferentiableAt_clm_of_components
    {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [FiniteDimensional ℝ F₁]
    {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
    (T : M → F₁ →L[ℝ] F₂) {ι : Type} [Fintype ι]
    (basis : Module.Basis ι ℝ F₁) {x : M}
    (h_components : ∀ i : ι, MDifferentiableAt I 𝓘(ℝ, F₂)
      (fun y : M => T y (basis i)) x) :
    MDifferentiableAt I 𝓘(ℝ, F₁ →L[ℝ] F₂) T x := by
  classical
  have h_decomp : T = fun y =>
      ∑ i, (basis.coord i).toContinuousLinearMap.smulRight (T y (basis i)) := by
    funext y
    ext v
    rw [ContinuousLinearMap.sum_apply]
    have hv : v = ∑ i, basis.repr v i • basis i := by simp
    conv_lhs => rw [hv]
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    simp [ContinuousLinearMap.smulRight_apply,
      LinearMap.coe_toContinuousLinearMap', Module.Basis.coord_apply,
      (T y).map_smul]
  rw [h_decomp]
  -- Convert (fun y => ∑ i, f i y) to (∑ i, fun y => f i y) for MDifferentiableAt.sum.
  have h_swap : (fun y : M => ∑ i,
      (basis.coord i).toContinuousLinearMap.smulRight (T y (basis i)))
      = (∑ i, fun y : M =>
          (basis.coord i).toContinuousLinearMap.smulRight (T y (basis i))) := by
    funext y
    rw [Finset.sum_apply]
  rw [h_swap]
  apply MDifferentiableAt.sum
  intro i _
  -- Each summand: smulRight applied to scalar component.
  -- (basis.coord i).toCLM.smulRight : F₂ →L (F₁ →L F₂) is a CLM, hence smooth.
  have h_smulRightL : ContMDiff 𝓘(ℝ, F₂) 𝓘(ℝ, F₁ →L[ℝ] F₂) ∞
      (fun w : F₂ => (basis.coord i).toContinuousLinearMap.smulRight w) := by
    have h_eq : (fun w : F₂ => (basis.coord i).toContinuousLinearMap.smulRight w)
        = ContinuousLinearMap.smulRightL ℝ F₁ F₂ (basis.coord i).toContinuousLinearMap := by
      funext w; rfl
    rw [h_eq]
    exact (ContinuousLinearMap.smulRightL ℝ F₁ F₂
      (basis.coord i).toContinuousLinearMap).contMDiff
  -- Apply MDifferentiableAt.comp
  have h_smulRightL_at :
      MDifferentiableAt 𝓘(ℝ, F₂) 𝓘(ℝ, F₁ →L[ℝ] F₂)
        (fun w => (basis.coord i).toContinuousLinearMap.smulRight w) (T x (basis i)) :=
    (h_smulRightL (T x (basis i))).mdifferentiableAt (by decide)
  exact h_smulRightL_at.comp x (h_components i)

omit [FiniteDimensional ℝ E] [IsLocallyConstantChartedSpace H M] g in
/-- **`mlieBracket` of two `ContMDiff` bundle sections is a smooth bundle section**.
Wrapper around Mathlib `ContMDiffAt.mlieBracket_vectorField` giving
`TangentSmoothAt` (framework's MDifferentiableAt-form predicate). -/
private theorem mlieBracket_tangentSmoothAt
    {U V : (y : M) → TangentSpace I y} {x : M}
    (hU : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (fun y => (⟨y, U y⟩ : TangentBundle I M)))
    (hV : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (fun y => (⟨y, V y⟩ : TangentBundle I M))) :
    OpenGALib.TangentSmoothAt (mlieBracket I U V) x := by
  -- IsManifold I a M auto-inferred from IsManifold I ∞ M + LEInfty a (Mathlib instance).
  haveI : IsManifold I (3 : ℕ∞ω) M := inferInstance
  haveI : IsManifold I (2 : ℕ∞ω) M := inferInstance
  haveI hM_2plus1 : IsManifold I (((2 : ℕ∞) : ℕ∞ω) + 1) M := by
    show IsManifold I (3 : ℕ∞ω) M
    infer_instance
  haveI : IsManifold I ((minSmoothness ℝ 2 : ℕ∞ω)) M := by
    rw [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  have h_min : minSmoothness ℝ ((1 : ℕ∞) + 1) ≤ (2 : ℕ∞) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    norm_num
  have hU2 : ContMDiffAt I (I.prod 𝓘(ℝ, E)) ((2 : ℕ∞) : ℕ∞ω)
      (fun y => (⟨y, U y⟩ : TangentBundle I M)) x :=
    (hU x).of_le (by exact_mod_cast le_top)
  have hV2 : ContMDiffAt I (I.prod 𝓘(ℝ, E)) ((2 : ℕ∞) : ℕ∞ω)
      (fun y => (⟨y, V y⟩ : TangentBundle I M)) x :=
    (hV x).of_le (by exact_mod_cast le_top)
  have h_mlb1 : ContMDiffAt I (I.prod 𝓘(ℝ, E)) ((1 : ℕ∞) : ℕ∞ω)
      (fun y => (⟨y, mlieBracket I U V y⟩ : TangentBundle I M)) x :=
    hU2.mlieBracket_vectorField hV2 h_min
  exact h_mlb1.mdifferentiableAt (by decide)

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

set_option backward.isDefEq.respectTransparency false in
/-- **Scalar smoothness of `koszulCotangentScalar v Y w` in `y`** at every `x`.

Decomposes into 6 koszul-term smoothness checks:
* 3 directional-derivative terms via `mfderiv_const_dir_smoothAt` /
  `mfderiv_smoothDir_smoothAt`.
* 3 mlieBracket-with-metric-inner terms via `mlieBracket_tangentSmoothAt` +
  `MDifferentiableAt.metricInner_smoothAt`.
Sum via `MDifferentiableAt.add` / `.sub` / `.const_mul`. -/
private theorem koszulCotangentScalar_mdifferentiableAt
    (v : E) (Y : SmoothVectorField I M) (w : E) (x : M) :
    MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y : M => koszulCotangentScalar v Y w y) x := by
  classical
  -- Smooth scalar functions used in the 6 koszul terms.
  have hY_E : ContMDiff I 𝓘(ℝ, E) ∞ Y.toFun := SmoothVectorField.contMDiff_E Y
  have h_const_v_E : ContMDiff I 𝓘(ℝ, E) ∞ (fun _ : M => v) := contMDiff_const
  have h_const_w_E : ContMDiff I 𝓘(ℝ, E) ∞ (fun _ : M => w) := contMDiff_const
  -- Scalar functions for terms 1, 2, 3 via metricInner_contMDiff.
  have h_f_YW : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun y' : M => metricInner (g := g) y' (Y.toFun y') w) := by
    have := metricInner_contMDiff hY_E h_const_w_E
    convert this using 1
  have h_f_WV : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun y' : M => metricInner (g := g) y' w v) := by
    have := metricInner_contMDiff h_const_w_E h_const_v_E
    convert this using 1
  have h_f_VY : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun y' : M => metricInner (g := g) y' v (Y.toFun y')) := by
    have := metricInner_contMDiff h_const_v_E hY_E
    convert this using 1
  -- TangentSmoothAt for the 3 const + Y bundle sections.
  have hY_y : OpenGALib.TangentSmoothAt Y.toFun x := Y.smoothAt x
  have h_const_v_y : OpenGALib.TangentSmoothAt (fun _ : M => v) x :=
    (SmoothVectorField.const (I := I) (M := M) v).smoothAt x
  have h_const_w_y : OpenGALib.TangentSmoothAt (fun _ : M => w) x :=
    (SmoothVectorField.const (I := I) (M := M) w).smoothAt x
  -- TangentSmoothAt of mlieBracket sections (T4, T5, T6).
  have h_mlb_vY : OpenGALib.TangentSmoothAt
      (mlieBracket I (fun _ : M => v) Y.toFun) x :=
    mlieBracket_tangentSmoothAt
      (SmoothVectorField.const (I := I) (M := M) v).smooth Y.smooth
  have h_mlb_Yw : OpenGALib.TangentSmoothAt
      (mlieBracket I Y.toFun (fun _ : M => w)) x :=
    mlieBracket_tangentSmoothAt Y.smooth
      (SmoothVectorField.const (I := I) (M := M) w).smooth
  have h_mlb_vw : OpenGALib.TangentSmoothAt
      (mlieBracket I (fun _ : M => v) (fun _ : M => w)) x :=
    mlieBracket_tangentSmoothAt
      (SmoothVectorField.const (I := I) (M := M) v).smooth
      (SmoothVectorField.const (I := I) (M := M) w).smooth
  -- 6 koszul terms in mfderiv form (skip directionalDeriv unfold step).
  have hT1 : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun y : M => mfderiv I 𝓘(ℝ, ℝ)
        (fun y' => metricInner (g := g) y' (Y.toFun y') w) y v) x :=
    mfderiv_const_dir_smoothAt h_f_YW x v
  have hT2 : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun y : M => mfderiv I 𝓘(ℝ, ℝ)
        (fun y' => metricInner (g := g) y' w v) y (Y.toFun y)) x :=
    mfderiv_smoothDir_smoothAt h_f_WV (hY_E.contMDiffAt)
  have hT3 : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun y : M => mfderiv I 𝓘(ℝ, ℝ)
        (fun y' => metricInner (g := g) y' v (Y.toFun y')) y w) x :=
    mfderiv_const_dir_smoothAt h_f_VY x w
  have hT4 : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun y : M => metricInner (g := g) y (mlieBracket I (fun _ : M => v) Y.toFun y) w) x :=
    MDifferentiableAt.metricInner_smoothAt h_mlb_vY h_const_w_y
  have hT5 : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun y : M => metricInner (g := g) y (mlieBracket I Y.toFun (fun _ : M => w) y) v) x :=
    MDifferentiableAt.metricInner_smoothAt h_mlb_Yw h_const_v_y
  have hT6 : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun y : M => metricInner (g := g) y
        (mlieBracket I (fun _ : M => v) (fun _ : M => w) y) (Y.toFun y)) x :=
    MDifferentiableAt.metricInner_smoothAt h_mlb_vw hY_y
  -- koszulCotangentScalar unfolds to (1/2) * koszulFunctional.
  -- koszulFunctional unfolds to T1 + T2 - T3 + T4 - T5 - T6 (directionalDeriv = mfderiv by def).
  unfold koszulCotangentScalar koszulFunctional directionalDeriv
  -- Goal: MDifferentiableAt of `fun y => (1/2) * (T1 + T2 - T3 + T4 - T5 - T6)` at x.
  exact ((((((hT1.add hT2).sub hT3).add hT4).sub hT5).sub hT6).const_smul (1/2 : ℝ))

/-- **Smoothness of the koszul cotangent CLM section** as `M → (E →L[ℝ] ℝ)`.
Componentwise lift of `koszulCotangentScalar_mdifferentiableAt` via
`mdifferentiableAt_clm_of_components` with `Module.finBasis ℝ E`. -/
theorem koszulCotangentCLM_smoothAt
    (v : E) (Y : SmoothVectorField I M) (x : M) :
    MDifferentiableAt I 𝓘(ℝ, E →L[ℝ] ℝ)
      (fun y : M => koszulCotangentCLM v Y y) x := by
  -- Componentwise lift: for each basis element b_i, the scalar
  -- (fun y => koszulCotangentCLM v Y y (b_i)) = (fun y => koszulCotangentScalar v Y b_i y)
  -- is MDifferentiableAt at x by koszulCotangentScalar_mdifferentiableAt.
  -- Lift to CLM via mdifferentiableAt_clm_of_components.
  set basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E := Module.finBasis ℝ E
  apply mdifferentiableAt_clm_of_components _ basis
  intro i
  show MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y : M => koszulCotangentCLM v Y y (basis i)) x
  have h_eq : (fun y : M => koszulCotangentCLM v Y y (basis i))
      = (fun y : M => koszulCotangentScalar v Y (basis i) y) := by
    funext y
    exact koszulCotangentCLM_apply v Y y (basis i)
  rw [h_eq]
  exact koszulCotangentScalar_mdifferentiableAt v Y (basis i) x

end Riemannian
