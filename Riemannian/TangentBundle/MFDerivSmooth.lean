import Riemannian.TangentBundle.Smoothness
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-!
# `mfderiv` smoothness for chart-frame-constant directions

For a globally smooth scalar function $f : M \to \mathbb{R}$ on a boundaryless
smooth manifold, and any chart-frame-constant direction $v : E$, the function
$y \mapsto df_y(v)$ is smooth at every $x$.

Specialization of Mathlib's `ContMDiffAt.mfderiv_apply` to ℝ-valued targets,
removing the `inTangentCoordinates` packaging via the chart-pullback identity:
$df_y = d(f \circ \text{chart.symm})_{\text{chart}(y)} \circ d\text{chart}_y$.

## Used by

* Koszul cotangent section smoothness
  (`Riemannian/Connection/KoszulCotangent.lean`).

**Ground truth**: standard chain rule for smooth maps to a normed space. -/

open scoped ContDiff Manifold Topology

namespace OpenGALib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [IsLocallyConstantChartedSpace H M]

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
set_option backward.isDefEq.respectTransparency false in
/-- **Smoothness of `mfderiv` applied to a chart-frame-constant direction**.

For a globally smooth scalar function $f : M \to \mathbb{R}$ and any $v : E$
(treated as a chart-frame-constant tangent direction via
`TangentSpace I y = E` def-eq), the function $y \mapsto df_y(v)$ is smooth
at every $x$.

Boundaryless model assumption: needed so that `chart.target ∈ 𝓝 (chart x)`
(via `extChartAt_target_mem_nhds`), letting us derive `ContDiffAt` of
`f ∘ chart.symm` at `chart x`.

Strategy: chart pullback. Define `f̂ := f ∘ (extChartAt I x).symm : E → ℝ`,
smooth on a nhd of `chart x`. By the chain rule on chart source,
$df_y(v) = d\hat{f}_{\text{chart}(y)}\big(d\text{chart}_y(v)\big)$. Smoothness
in $y$ follows from `ContDiffAt.fderiv_right` (smoothness of `fderiv`) +
`mfderiv_extChartAt_apply_smoothAt` (framework: chart mfderiv smooth in
basepoint) via `clm_apply`. -/
theorem mfderiv_const_dir_smoothAt
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M) (v : E) :
    MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y : M => mfderiv I 𝓘(ℝ, ℝ) f y v) x := by
  -- chart.target ∈ 𝓝 (chart x) under I.Boundaryless.
  have h_target_nhds : (extChartAt I x).target ∈ 𝓝 (extChartAt I x x) :=
    extChartAt_target_mem_nhds x
  -- Step 1: f̂ = f ∘ chart.symm smooth at chart x in normed sense.
  have h_f_hat : ContDiffAt ℝ ∞ (f ∘ (extChartAt I x).symm) (extChartAt I x x) := by
    have h_symm_on : ContMDiffOn 𝓘(ℝ, E) I ∞ (extChartAt I x).symm
        (extChartAt I x).target := contMDiffOn_extChartAt_symm x
    have h_symm_at : ContMDiffAt 𝓘(ℝ, E) I ∞ (extChartAt I x).symm
        (extChartAt I x x) :=
      h_symm_on.contMDiffAt h_target_nhds
    have h_eqx : (extChartAt I x).symm (extChartAt I x x) = x := by simp
    have h_comp : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞
        (f ∘ (extChartAt I x).symm) (extChartAt I x x) :=
      (hf x).comp_of_eq h_symm_at h_eqx
    rw [contMDiffAt_iff_contDiffAt] at h_comp
    exact h_comp
  -- Step 2: fderiv ℝ f̂ smooth at chart x; compose with smooth chart.
  have h_fderiv_at : ContDiffAt ℝ ∞ (fderiv ℝ (f ∘ (extChartAt I x).symm))
      (extChartAt I x x) :=
    h_f_hat.fderiv_right (le_refl _)
  have h_chart_at : ContMDiffAt I 𝓘(ℝ, E) ∞ (extChartAt I x : M → E) x :=
    contMDiffAt_extChartAt
  have h_fderiv_chart_at : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] ℝ) ∞
      (fun y : M => fderiv ℝ (f ∘ (extChartAt I x).symm) (extChartAt I x y)) x :=
    h_fderiv_at.contMDiffAt.comp x h_chart_at
  -- Step 3: (fun y => mfderiv chart y v) smooth at x.
  have h_chart_mfderiv_at : ContMDiffAt I 𝓘(ℝ, E) ∞
      (fun y : M => mfderiv I 𝓘(ℝ, E) (extChartAt I x : M → E) y v) x := by
    have h_cLMA := TangentBundle.continuousLinearMapAtFlat_contMDiffAt
      (I := I) (M := M) x
    have h_apply : ContMDiffAt I 𝓘(ℝ, E) ∞
        (fun y : M =>
          TangentBundle.continuousLinearMapAtFlat (I := I) (M := M) x y v) x :=
      h_cLMA.clm_apply contMDiffAt_const
    apply h_apply.congr_of_eventuallyEq
    have h_chart_src : (chartAt H x).source ∈ 𝓝 x :=
      (chartAt H x).open_source.mem_nhds (mem_chart_source H x)
    filter_upwards [h_chart_src] with y hy
    show mfderiv I 𝓘(ℝ, E) (extChartAt I x : M → E) y v
      = TangentBundle.continuousLinearMapAtFlat (I := I) (M := M) x y v
    show mfderiv I 𝓘(ℝ, E) (extChartAt I x : M → E) y v
      = (trivializationAt E (TangentSpace I) x).continuousLinearMapAt ℝ y v
    rw [TangentBundle.continuousLinearMapAt_trivializationAt hy]
    rfl
  -- Step 4: clm_apply.
  have h_compose : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun y : M => fderiv ℝ (f ∘ (extChartAt I x).symm) (extChartAt I x y)
        (mfderiv I 𝓘(ℝ, E) (extChartAt I x : M → E) y v)) x :=
    h_fderiv_chart_at.clm_apply h_chart_mfderiv_at
  -- Step 5: equate with `mfderiv f y v` via chain rule on chart source nhd.
  have h_top_ne : (∞ : ℕ∞ω) ≠ 0 := by decide
  apply (h_compose.mdifferentiableAt h_top_ne).congr_of_eventuallyEq
  have h_chart_src : (chartAt H x).source ∈ 𝓝 x :=
    (chartAt H x).open_source.mem_nhds (mem_chart_source H x)
  filter_upwards [h_chart_src] with y hy
  have hy_ext : y ∈ (extChartAt I x).source := by
    rwa [extChartAt_source]
  -- chart at y differentiable.
  have h_chart_diff : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I x : M → E) y :=
    mdifferentiableAt_extChartAt hy
  -- chart.symm differentiable at chart y.
  have h_chart_y_in_target : extChartAt I x y ∈ (extChartAt I x).target :=
    (extChartAt I x).map_source hy_ext
  have h_target_nhds_y : (extChartAt I x).target ∈ 𝓝 (extChartAt I x y) :=
    (isOpen_extChartAt_target x).mem_nhds h_chart_y_in_target
  have h_symm_diff : MDifferentiableAt 𝓘(ℝ, E) I (extChartAt I x).symm
      (extChartAt I x y) :=
    ((contMDiffOn_extChartAt_symm x).mdifferentiableOn h_top_ne).mdifferentiableAt
      h_target_nhds_y
  have hf_at_y : MDifferentiableAt I 𝓘(ℝ, ℝ) f y :=
    (hf y).mdifferentiableAt h_top_ne
  have h_eq_y_back : ((extChartAt I x).symm) (extChartAt I x y) = y :=
    (extChartAt I x).left_inv hy_ext
  -- f ∘ chart.symm differentiable at chart y, with value at chart y equal to f y.
  have h_f_diff : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (f ∘ (extChartAt I x).symm)
      (extChartAt I x y) := by
    have := MDifferentiableAt.comp (extChartAt I x y) (h_eq_y_back ▸ hf_at_y) h_symm_diff
    exact this
  have h_factor : (f : M → ℝ) =ᶠ[𝓝 y]
      ((f ∘ (extChartAt I x).symm) ∘ (extChartAt I x : M → E)) := by
    have h_chart_src_y : (chartAt H x).source ∈ 𝓝 y :=
      (chartAt H x).open_source.mem_nhds hy
    filter_upwards [h_chart_src_y] with z hz
    show f z = (f ∘ (extChartAt I x).symm) ((extChartAt I x : M → E) z)
    have hz_ext : z ∈ (extChartAt I x).source := by rwa [extChartAt_source]
    show f z = f ((extChartAt I x).symm ((extChartAt I x : M → E) z))
    rw [(extChartAt I x).left_inv hz_ext]
  have h_mfderiv_eq : mfderiv I 𝓘(ℝ, ℝ) f y
      = mfderiv I 𝓘(ℝ, ℝ)
          ((f ∘ (extChartAt I x).symm) ∘ (extChartAt I x : M → E)) y :=
    Filter.EventuallyEq.mfderiv_eq h_factor
  show (mfderiv I 𝓘(ℝ, ℝ) f y) v
    = (fderiv ℝ (f ∘ (extChartAt I x).symm) (extChartAt I x y))
        ((mfderiv I 𝓘(ℝ, E) (extChartAt I x : M → E) y) v)
  calc (mfderiv I 𝓘(ℝ, ℝ) f y) v
      = (mfderiv I 𝓘(ℝ, ℝ)
          ((f ∘ (extChartAt I x).symm) ∘ ((extChartAt I x) : M → E)) y) v :=
        congrArg (fun (m : TangentSpace I y →L[ℝ] ℝ) => m v) h_mfderiv_eq
    _ = (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (f ∘ (extChartAt I x).symm) (extChartAt I x y))
            ((mfderiv I 𝓘(ℝ, E) ((extChartAt I x) : M → E) y) v) := by
        rw [mfderiv_comp _ h_f_diff h_chart_diff]
        rfl
    _ = (fderiv ℝ (f ∘ (extChartAt I x).symm) (extChartAt I x y))
          ((mfderiv I 𝓘(ℝ, E) ((extChartAt I x) : M → E) y) v) := by
        congr 1
        exact mfderiv_eq_fderiv

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
set_option backward.isDefEq.respectTransparency false in
/-- **Smoothness of `mfderiv` applied to a smooth direction**.

Generalization of `mfderiv_const_dir_smoothAt` to varying directions: for a
globally smooth scalar function $f : M \to \mathbb{R}$ and a section
$V : M \to E$ smooth at $x$ (treated as a tangent direction via
`TangentSpace I y = E` def-eq), the function $y \mapsto df_y(V_y)$ is smooth
at $x$.

Same chart-pullback strategy as `mfderiv_const_dir_smoothAt`, but the
direction term is `mfderiv chart y (V y)` (smooth in y via `clm_apply`)
instead of `mfderiv chart y v` (smooth in y for fixed v). -/
theorem mfderiv_smoothDir_smoothAt
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {x : M}
    {V : M → E} (hV : ContMDiffAt I 𝓘(ℝ, E) ∞ V x) :
    MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun y : M => mfderiv I 𝓘(ℝ, ℝ) f y (V y)) x := by
  have h_target_nhds : (extChartAt I x).target ∈ 𝓝 (extChartAt I x x) :=
    extChartAt_target_mem_nhds x
  -- Step 1: f̂ = f ∘ chart.symm smooth at chart x in normed sense.
  have h_f_hat : ContDiffAt ℝ ∞ (f ∘ (extChartAt I x).symm) (extChartAt I x x) := by
    have h_symm_on : ContMDiffOn 𝓘(ℝ, E) I ∞ (extChartAt I x).symm
        (extChartAt I x).target := contMDiffOn_extChartAt_symm x
    have h_symm_at : ContMDiffAt 𝓘(ℝ, E) I ∞ (extChartAt I x).symm
        (extChartAt I x x) :=
      h_symm_on.contMDiffAt h_target_nhds
    have h_eqx : (extChartAt I x).symm (extChartAt I x x) = x := by simp
    have h_comp : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞
        (f ∘ (extChartAt I x).symm) (extChartAt I x x) :=
      (hf x).comp_of_eq h_symm_at h_eqx
    rw [contMDiffAt_iff_contDiffAt] at h_comp
    exact h_comp
  -- Step 2: fderiv ℝ f̂ smooth; compose with smooth chart.
  have h_fderiv_at : ContDiffAt ℝ ∞ (fderiv ℝ (f ∘ (extChartAt I x).symm))
      (extChartAt I x x) :=
    h_f_hat.fderiv_right (le_refl _)
  have h_chart_at : ContMDiffAt I 𝓘(ℝ, E) ∞ (extChartAt I x : M → E) x :=
    contMDiffAt_extChartAt
  have h_fderiv_chart_at : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] ℝ) ∞
      (fun y : M => fderiv ℝ (f ∘ (extChartAt I x).symm) (extChartAt I x y)) x :=
    h_fderiv_at.contMDiffAt.comp x h_chart_at
  -- Step 3: (fun y => mfderiv chart y (V y)) smooth via continuousLinearMapAtFlat
  -- (which has flat type E →L[ℝ] E) clm_apply with smooth V.
  have h_cLMA : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E) ∞
      (TangentBundle.continuousLinearMapAtFlat (I := I) (M := M) x) x :=
    TangentBundle.continuousLinearMapAtFlat_contMDiffAt (I := I) (M := M) x
  have h_apply_flat : ContMDiffAt I 𝓘(ℝ, E) ∞
      (fun y : M =>
        TangentBundle.continuousLinearMapAtFlat (I := I) (M := M) x y (V y)) x :=
    h_cLMA.clm_apply hV
  have h_mfderiv_chart_V : ContMDiffAt I 𝓘(ℝ, E) ∞
      (fun y : M => mfderiv I 𝓘(ℝ, E) (extChartAt I x : M → E) y (V y)) x := by
    apply h_apply_flat.congr_of_eventuallyEq
    have h_chart_src : (chartAt H x).source ∈ 𝓝 x :=
      (chartAt H x).open_source.mem_nhds (mem_chart_source H x)
    filter_upwards [h_chart_src] with y hy
    show mfderiv I 𝓘(ℝ, E) (extChartAt I x : M → E) y (V y)
      = TangentBundle.continuousLinearMapAtFlat (I := I) (M := M) x y (V y)
    show mfderiv I 𝓘(ℝ, E) (extChartAt I x : M → E) y (V y)
      = (trivializationAt E (TangentSpace I) x).continuousLinearMapAt ℝ y (V y)
    rw [TangentBundle.continuousLinearMapAt_trivializationAt hy]
    rfl
  -- Step 4: clm_apply.
  have h_compose : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun y : M => fderiv ℝ (f ∘ (extChartAt I x).symm) (extChartAt I x y)
        (mfderiv I 𝓘(ℝ, E) (extChartAt I x : M → E) y (V y))) x :=
    h_fderiv_chart_at.clm_apply h_mfderiv_chart_V
  -- Step 5: equate via chain rule on chart source nhd.
  have h_top_ne : (∞ : ℕ∞ω) ≠ 0 := by decide
  apply (h_compose.mdifferentiableAt h_top_ne).congr_of_eventuallyEq
  have h_chart_src : (chartAt H x).source ∈ 𝓝 x :=
    (chartAt H x).open_source.mem_nhds (mem_chart_source H x)
  filter_upwards [h_chart_src] with y hy
  have hy_ext : y ∈ (extChartAt I x).source := by
    rwa [extChartAt_source]
  have h_chart_diff : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I x : M → E) y :=
    mdifferentiableAt_extChartAt hy
  have h_chart_y_in_target : extChartAt I x y ∈ (extChartAt I x).target :=
    (extChartAt I x).map_source hy_ext
  have h_target_nhds_y : (extChartAt I x).target ∈ 𝓝 (extChartAt I x y) :=
    (isOpen_extChartAt_target x).mem_nhds h_chart_y_in_target
  have h_symm_diff : MDifferentiableAt 𝓘(ℝ, E) I (extChartAt I x).symm
      (extChartAt I x y) :=
    ((contMDiffOn_extChartAt_symm x).mdifferentiableOn h_top_ne).mdifferentiableAt
      h_target_nhds_y
  have hf_at_y : MDifferentiableAt I 𝓘(ℝ, ℝ) f y :=
    (hf y).mdifferentiableAt h_top_ne
  have h_eq_y_back : ((extChartAt I x).symm) (extChartAt I x y) = y :=
    (extChartAt I x).left_inv hy_ext
  have h_f_diff : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (f ∘ (extChartAt I x).symm)
      (extChartAt I x y) := by
    have := MDifferentiableAt.comp (extChartAt I x y) (h_eq_y_back ▸ hf_at_y) h_symm_diff
    exact this
  have h_factor : (f : M → ℝ) =ᶠ[𝓝 y]
      ((f ∘ (extChartAt I x).symm) ∘ (extChartAt I x : M → E)) := by
    have h_chart_src_y : (chartAt H x).source ∈ 𝓝 y :=
      (chartAt H x).open_source.mem_nhds hy
    filter_upwards [h_chart_src_y] with z hz
    show f z = (f ∘ (extChartAt I x).symm) ((extChartAt I x : M → E) z)
    have hz_ext : z ∈ (extChartAt I x).source := by rwa [extChartAt_source]
    show f z = f ((extChartAt I x).symm ((extChartAt I x : M → E) z))
    rw [(extChartAt I x).left_inv hz_ext]
  have h_mfderiv_eq : mfderiv I 𝓘(ℝ, ℝ) f y
      = mfderiv I 𝓘(ℝ, ℝ)
          ((f ∘ (extChartAt I x).symm) ∘ (extChartAt I x : M → E)) y :=
    Filter.EventuallyEq.mfderiv_eq h_factor
  show (mfderiv I 𝓘(ℝ, ℝ) f y) (V y)
    = (fderiv ℝ (f ∘ (extChartAt I x).symm) (extChartAt I x y))
        ((mfderiv I 𝓘(ℝ, E) (extChartAt I x : M → E) y) (V y))
  calc (mfderiv I 𝓘(ℝ, ℝ) f y) (V y)
      = (mfderiv I 𝓘(ℝ, ℝ)
          ((f ∘ (extChartAt I x).symm) ∘ ((extChartAt I x) : M → E)) y) (V y) :=
        congrArg (fun (m : TangentSpace I y →L[ℝ] ℝ) => m (V y)) h_mfderiv_eq
    _ = (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (f ∘ (extChartAt I x).symm) (extChartAt I x y))
            ((mfderiv I 𝓘(ℝ, E) ((extChartAt I x) : M → E) y) (V y)) := by
        rw [mfderiv_comp _ h_f_diff h_chart_diff]
        rfl
    _ = (fderiv ℝ (f ∘ (extChartAt I x).symm) (extChartAt I x y))
          ((mfderiv I 𝓘(ℝ, E) ((extChartAt I x) : M → E) y) (V y)) := by
        congr 1
        exact mfderiv_eq_fderiv

end OpenGALib
