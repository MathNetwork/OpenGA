import Mathlib.Geometry.Manifold.VectorBundle.Tensoriality
import Mathlib.Geometry.Manifold.VectorField.LieBracket
import OpenGALib.Riemannian.Manifold.SmoothManifold
import OpenGALib.Riemannian.Util.Metric.MetricInnerSmoothness
import OpenGALib.Riemannian.TangentBundle.TangentSmooth
import OpenGALib.Riemannian.TensorBundle.MusicalIso
import OpenGALib.Riemannian.Util.Tangent.MfderivApplySection
import OpenGALib.Riemannian.Connection.Koszul
import OpenGALib.Riemannian.Connection.RieszExtraction
import OpenGALib.Riemannian.Util.Tangent.TangentHelpers

/-!
# Tensoriality + smoothness machinery for `koszulCovDeriv`

Engineering scaffolding under the Levi-Civita existence proof. Two pieces:

* `koszulCovDerivAux` + `koszulCovDerivAux_tensorialAt` — smoothness-erased
  variant of `koszulCovDeriv` in the `X` argument, with $C^\infty(M)$-linearity
  in `X` lifted from `koszul_smul_left` / `koszul_add_left` via Riesz
  uniqueness. Required because Mathlib's `TensorialAt` quantifies over all
  sections, not just smooth ones; `TensorialAt.mkHom` then packages
  $\nabla_\cdot Y(x)$ as a `T_xM →L[ℝ] T_xM`.

* `koszulCovDeriv_smoothVF_smoothAt` + `koszulCovDeriv_const_smoothAt` —
  smoothness of $y \mapsto \nabla_{X(y)}Y(y)$ under smooth inputs. Identifies
  `koszulCovDeriv` with `g.metricRiesz y (Φ y)` via Riesz uniqueness, then
  reduces through `g.metricRiesz_section_contMDiffAt_of_within` to per-chart-
  basis-index `ContMDiffWithinAt` of the six Koszul terms, transferred from a
  bumped global extension via `koszulFunctional_local`.

Both feed `koszulLeviCivita_exists` and the smoothness clause of
`leviCivitaConnection_exists` in `Connection.lean`.
-/

open Bundle VectorField
open scoped ContDiff Manifold Topology Riemannian

namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [hm : HasMetric I M]

/-! ### Smoothness-erased aux + tensoriality in `X` -/

/-- **Eng.** Smoothness-erased version of `koszulCovDeriv` in the `X`
argument: returns `koszulCovDeriv X Y x hX hY` for smooth `X`, `0`
otherwise. Required because Mathlib's `TensorialAt` quantifies over all
sections, not just smooth ones. -/
noncomputable def koszulCovDerivAux
    [IsLocallyConstantChartedSpace H M]
    (g : RiemannianMetric I M)
    (Y : VectorFieldSection I M) (x : M) (hY : TangentSmoothAt Y x)
    (X : VectorFieldSection I M) : TangentSpace I x := by
  classical
  exact if hX : TangentSmoothAt X x then koszulCovDeriv g X Y x hX hY else 0

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [T2Space M] in
/-- **Mixed.** Tensoriality of `koszulCovDerivAux g Y x hY` in the `X`
argument. Math: $\nabla_\cdot Y$ is $C^\infty(M)$-linear in $X$ (`koszul_smul_left`,
`koszul_add_left`). Eng: lifted from `koszulFunctional` to `koszulCovDeriv`
through `g.metricInner_eq_iff_eq` against extended test vectors. -/
theorem koszulCovDerivAux_tensorialAt
    [IsLocallyConstantChartedSpace H M]
    (g : RiemannianMetric I M)
    (Y : VectorFieldSection I M) (x : M) (hY : TangentSmoothAt Y x) :
    TensorialAt I E (koszulCovDerivAux g Y x hY) x where
  smul := by
    intro f X hf hX_raw
    classical
    have hX : TangentSmoothAt X x := hX_raw
    have h_fX : TangentSmoothAt (f • X) x := TangentSmoothAt.smul hf hX
    show koszulCovDerivAux g Y x hY (f • X) = f x • koszulCovDerivAux g Y x hY X
    simp only [koszulCovDerivAux, dif_pos hX, dif_pos h_fX]
    apply (g.metricInner_eq_iff_eq x _ _).mp
    intro Z₀
    set Z : VectorFieldSection I M := FiberBundle.extend E Z₀
    have hZ_smooth : TangentSmoothAt Z x :=
      FiberBundle.mdifferentiableAt_extend I E Z₀
    have hZx : Z x = Z₀ := FiberBundle.extend_apply_self _ _
    have h_ZX := g.metricInner_mdifferentiableAt hZ_smooth hX
    have h_XY := g.metricInner_mdifferentiableAt hX hY
    have h_smul_left :
        koszulFunctional g (f • X) Y Z x = f x * koszulFunctional g X Y Z x :=
      koszul_smul_left g X Y Z f x hf h_ZX h_XY hX
    rw [← hZx,
        koszulCovDeriv_inner_eq g _ _ _ x h_fX hY hZ_smooth,
        h_smul_left,
        g.metricInner_smul_left,
        koszulCovDeriv_inner_eq g X Y Z x hX hY hZ_smooth]
    ring
  add := by
    intro X X' hX_raw hX'_raw
    classical
    have hX : TangentSmoothAt X x := hX_raw
    have hX' : TangentSmoothAt X' x := hX'_raw
    have h_sum : TangentSmoothAt (X + X') x := TangentSmoothAt.add hX hX'
    show koszulCovDerivAux g Y x hY (X + X')
        = koszulCovDerivAux g Y x hY X + koszulCovDerivAux g Y x hY X'
    simp only [koszulCovDerivAux, dif_pos hX, dif_pos hX', dif_pos h_sum]
    apply (g.metricInner_eq_iff_eq x _ _).mp
    intro Z₀
    set Z : VectorFieldSection I M := FiberBundle.extend E Z₀
    have hZ_smooth : TangentSmoothAt Z x :=
      FiberBundle.mdifferentiableAt_extend I E Z₀
    have hZx : Z x = Z₀ := FiberBundle.extend_apply_self _ _
    have h_ZX₁ := g.metricInner_mdifferentiableAt hZ_smooth hX
    have h_ZX₂ := g.metricInner_mdifferentiableAt hZ_smooth hX'
    have h_X₁Y := g.metricInner_mdifferentiableAt hX hY
    have h_X₂Y := g.metricInner_mdifferentiableAt hX' hY
    have h_add_left :
        koszulFunctional g (X + X') Y Z x
          = koszulFunctional g X Y Z x + koszulFunctional g X' Y Z x :=
      koszul_add_left g X X' Y Z x h_ZX₁ h_ZX₂ h_X₁Y h_X₂Y hX hX'
    rw [← hZx,
        koszulCovDeriv_inner_eq g _ _ _ x h_sum hY hZ_smooth,
        h_add_left,
        g.metricInner_add_left,
        koszulCovDeriv_inner_eq g X Y Z x hX hY hZ_smooth,
        koszulCovDeriv_inner_eq g X' Y Z x hX' hY hZ_smooth]
    ring

/-! ### Bridge: smoothness of `koszulCovDeriv g X.toFun Y.toFun y` at `x` -/

/-- **Mixed.** For `X, Y : SmoothVectorField I M`, the section
`y ↦ koszulCovDeriv g X.toFun Y.toFun y` is `TangentSmoothAt` everywhere.

Math: smoothness of the Levi-Civita section under smooth inputs.
Eng: identifies `koszulCovDeriv` with `g.metricRiesz y (Φ y)` via Riesz
uniqueness, then reduces through `g.metricRiesz_section_contMDiffAt_of_within`
to per-chart-basis-index ContMDiffWithinAt of the six Koszul terms
transferred from a bumped global extension via `koszulFunctional_local`. -/
theorem koszulCovDeriv_smoothVF_smoothAt
    [IsLocallyConstantChartedSpace H M]
    (g : RiemannianMetric I M)
    (X Y : SmoothVectorField I M) (x : M) :
    TangentSmoothAt
      (fun y : M => koszulCovDeriv g X.toFun Y.toFun y
        (X.smoothAt y) (Y.smoothAt y)) x := by
  classical
  -- Step 1: Identify `koszulCovDeriv X Y y h h = g.metricRiesz y (Φ y)` via Riesz uniqueness.
  set Φ : (y : M) → TangentSpace I y →L[ℝ] ℝ := fun y =>
    TensorialAt.mkHom _ y
      (koszulFunctional_tensorialAt g X.toFun Y.toFun y
        (X.smoothAt y) (Y.smoothAt y))
  have hRiesz : ∀ y : M,
      koszulCovDeriv g X.toFun Y.toFun y (X.smoothAt y) (Y.smoothAt y)
        = g.metricRiesz y (Φ y) := by
    intro y
    refine g.metricRiesz_unique y _ (Φ y) ?_
    intro W
    set V : VectorFieldSection I M := FiberBundle.extend E W
    have hV_smooth : TangentSmoothAt V y :=
      FiberBundle.mdifferentiableAt_extend I E W
    have hVy : V y = W := FiberBundle.extend_apply_self _ _
    rw [← hVy]
    rw [koszulCovDeriv_inner_eq g X.toFun Y.toFun V y
      (X.smoothAt y) (Y.smoothAt y) hV_smooth]
    exact (TensorialAt.mkHom_apply
      (koszulFunctional_tensorialAt g X.toFun Y.toFun y
        (X.smoothAt y) (Y.smoothAt y)) hV_smooth).symm
  have h_eq : (fun y : M =>
        koszulCovDeriv g X.toFun Y.toFun y (X.smoothAt y) (Y.smoothAt y))
      = (fun y : M => g.metricRiesz y (Φ y)) := funext hRiesz
  rw [h_eq]
  -- Step 2: apply `g.metricRiesz_section_contMDiffAt_of_within` with α := x.
  have hx_base : x ∈ (trivializationAt E (TangentSpace I) x).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet (𝕜 := ℝ) (I := I) x]
    exact mem_chart_source H x
  refine TangentSmoothAt.mk
    ((Riemannian.Tensor.metricRiesz_section_contMDiffAt_of_within
      g (α := x) hx_base (Φ := Φ) ?_).mdifferentiableAt
      (by simp : (∞ : ℕ∞ω) ≠ 0))
  -- Step 3: per-j ContMDiffWithinAt for `y ↦ Φ y (chartBasisVecFiber x j y)` at `x`.
  intro j
  obtain ⟨bump⟩ : Nonempty (SmoothBumpFunction I x) := inferInstance
  set chartBV : VectorFieldSection I M :=
    fun y => Riemannian.Tensor.chartBasisVecFiber (I := I) x j y with hchartBV_def
  set Ztilde : VectorFieldSection I M := fun y => bump y • chartBV y with hZtilde_def
  have htsupp : tsupport bump ⊆ (chartAt H x).source :=
    bump.tsupport_subset_chartAt_source
  have htriv_base : (trivializationAt E (TangentSpace I) x).baseSet =
      (chartAt H x).source :=
    TangentBundle.trivializationAt_baseSet (𝕜 := ℝ) (I := I) x
  have hbump_smoothOn :
      ContMDiffOn I 𝓘(ℝ) ∞ (fun y => bump y) (chartAt H x).source :=
    bump.contMDiff.contMDiffOn
  have hchartBV_smooth_on : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun y => (TotalSpace.mk' E y (chartBV y) :
        TotalSpace E (TangentSpace I : M → Type _)))
      (chartAt H x).source := by
    have := Riemannian.Tensor.chartBasisVec_contMDiffOn (I := I) x j
    rw [htriv_base] at this
    exact this
  have hZtilde_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun y => (TotalSpace.mk' E y (Ztilde y) :
        TotalSpace E (TangentSpace I : M → Type _))) := by
    have hkey := ContMDiffOn.smul_section_of_tsupport (𝕜 := ℝ) (n := ∞)
      (s := chartBV) (ψ := fun y => bump y) (u := (chartAt H x).source)
      hbump_smoothOn (chartAt H x).open_source htsupp hchartBV_smooth_on
    exact hkey
  let Ztilde_VF : SmoothVectorField I M := ⟨Ztilde, hZtilde_smooth⟩
  let U : Set M := interior {y : M | bump y = 1}
  have hU_open : IsOpen U := isOpen_interior
  have hx_U : x ∈ U := by
    have hb1 : bump =ᶠ[nhds x] 1 := bump.eventuallyEq_one
    have hsub : {y | bump y = 1} ∈ nhds x := by
      filter_upwards [hb1] with y hy
      exact hy
    exact mem_interior_iff_mem_nhds.mpr hsub
  have hU_subset_base : U ⊆ (trivializationAt E (TangentSpace I) x).baseSet := by
    rw [htriv_base]
    refine subset_trans interior_subset ?_
    intro y hy
    have hy_eq : bump y = 1 := hy
    have hy_supp : y ∈ Function.support (fun z => bump z) := by
      simp only [Function.mem_support]; rw [hy_eq]; norm_num
    have : y ∈ tsupport bump := subset_tsupport _ hy_supp
    exact htsupp this
  have hbumpOne_in_nhd : ∀ y ∈ U, {z : M | bump z = 1} ∈ nhds y := by
    intro y hy
    exact mem_interior_iff_mem_nhds.mp hy
  have hZtilde_local : ∀ y ∈ U,
      koszulFunctional g X.toFun Y.toFun Ztilde y
        = koszulFunctional g X.toFun Y.toFun chartBV y := by
    intro y hy
    refine koszulFunctional_local g X.toFun Y.toFun Ztilde chartBV y ?_
    filter_upwards [hbumpOne_in_nhd y hy] with z hz
    show bump z • chartBV z = chartBV z
    rw [show bump z = 1 from hz, one_smul]
  have h_YZtilde_inner : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun y' => g.metricInner y' (Y.toFun y') (Ztilde y')) :=
    g.metricInner_contMDiff Y.smooth hZtilde_smooth
  have h_ZtildeX_inner : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun y' => g.metricInner y' (Ztilde y') (X.toFun y')) :=
    g.metricInner_contMDiff hZtilde_smooth X.smooth
  have h_XY_inner : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun y' => g.metricInner y' (X.toFun y') (Y.toFun y')) :=
    g.metricInner_contMDiff X.smooth Y.smooth
  have hT1_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun y => directionalDeriv (fun y' => g.metricInner y' (Y.toFun y') (Ztilde y')) y
        (X.toFun y)) := by
    unfold directionalDeriv
    exact Riemannian.Tensor.mfderiv_apply_section_contMDiff (I := I)
      h_YZtilde_inner X.smooth
  have hT2_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun y => directionalDeriv (fun y' => g.metricInner y' (Ztilde y') (X.toFun y')) y
        (Y.toFun y)) := by
    unfold directionalDeriv
    exact Riemannian.Tensor.mfderiv_apply_section_contMDiff (I := I)
      h_ZtildeX_inner Y.smooth
  have hT3_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun y => directionalDeriv (fun y' => g.metricInner y' (X.toFun y') (Y.toFun y')) y
        (Ztilde y)) := by
    unfold directionalDeriv
    exact Riemannian.Tensor.mfderiv_apply_section_contMDiff (I := I)
      h_XY_inner hZtilde_smooth
  haveI : IsManifold I (minSmoothness ℝ 2) M := by
    rw [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  haveI hIM_succ : IsManifold I ((∞ : ℕ∞ω) + 1) M := by
    have h_eq : (∞ : ℕ∞ω) + 1 = ∞ := by
      change ((⊤ : ℕ∞) : ℕ∞ω) + (1 : ℕ∞ω) = ((⊤ : ℕ∞) : ℕ∞ω)
      rfl
    rw [h_eq]
    infer_instance
  have h_brXY_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun y => (TotalSpace.mk' E y (mlieBracket I X.toFun Y.toFun y) :
        TotalSpace E (TangentSpace I : M → Type _))) := by
    intro y
    exact X.smooth.contMDiffAt.mlieBracket_vectorField Y.smooth.contMDiffAt (by simp)
  have h_brYZtilde_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun y => (TotalSpace.mk' E y (mlieBracket I Y.toFun Ztilde y) :
        TotalSpace E (TangentSpace I : M → Type _))) := by
    intro y
    exact Y.smooth.contMDiffAt.mlieBracket_vectorField hZtilde_smooth.contMDiffAt (by simp)
  have h_brXZtilde_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun y => (TotalSpace.mk' E y (mlieBracket I X.toFun Ztilde y) :
        TotalSpace E (TangentSpace I : M → Type _))) := by
    intro y
    exact X.smooth.contMDiffAt.mlieBracket_vectorField hZtilde_smooth.contMDiffAt (by simp)
  have hT4_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun y => g.metricInner y (mlieBracket I X.toFun Y.toFun y) (Ztilde y)) :=
    g.metricInner_contMDiff h_brXY_smooth hZtilde_smooth
  have hT5_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun y => g.metricInner y (mlieBracket I Y.toFun Ztilde y) (X.toFun y)) :=
    g.metricInner_contMDiff h_brYZtilde_smooth X.smooth
  have hT6_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun y => g.metricInner y (mlieBracket I X.toFun Ztilde y) (Y.toFun y)) :=
    g.metricInner_contMDiff h_brXZtilde_smooth Y.smooth
  have hKoszul_Ztilde_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun y => koszulFunctional g X.toFun Y.toFun Ztilde y) := by
    show ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun y =>
      directionalDeriv (fun y' => g.metricInner y' (Y.toFun y') (Ztilde y')) y (X.toFun y)
      + directionalDeriv (fun y' => g.metricInner y' (Ztilde y') (X.toFun y')) y (Y.toFun y)
      - directionalDeriv (fun y' => g.metricInner y' (X.toFun y') (Y.toFun y')) y (Ztilde y)
      + g.metricInner y (mlieBracket I X.toFun Y.toFun y) (Ztilde y)
      - g.metricInner y (mlieBracket I Y.toFun Ztilde y) (X.toFun y)
      - g.metricInner y (mlieBracket I X.toFun Ztilde y) (Y.toFun y))
    exact ((((hT1_smooth.add hT2_smooth).sub hT3_smooth).add hT4_smooth).sub
      hT5_smooth).sub hT6_smooth
  have hKoszul_chartBV_on_U :
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞
        (fun y => (1 / 2 : ℝ) * koszulFunctional g X.toFun Y.toFun chartBV y) U := by
    have hKoszulZtilde_half : ContMDiffOn I 𝓘(ℝ, ℝ) ∞
        (fun y => (1 / 2 : ℝ) * koszulFunctional g X.toFun Y.toFun Ztilde y) U :=
      (contMDiffOn_const.mul hKoszul_Ztilde_smooth.contMDiffOn)
    refine hKoszulZtilde_half.congr ?_
    intro y hy
    rw [hZtilde_local y hy]
  have hKoszul_chartBV_at_x :
      ContMDiffAt I 𝓘(ℝ, ℝ) ∞
        (fun y => (1 / 2 : ℝ) * koszulFunctional g X.toFun Y.toFun chartBV y) x :=
    (hKoszul_chartBV_on_U x hx_U).contMDiffAt (hU_open.mem_nhds hx_U)
  have hbaseSet_open : IsOpen (trivializationAt E (TangentSpace I) x).baseSet :=
    (trivializationAt E (TangentSpace I) x).open_baseSet
  have hPhi_eq : ∀ y ∈ (trivializationAt E (TangentSpace I) x).baseSet,
      Φ y (chartBV y)
        = (1 / 2 : ℝ) * koszulFunctional g X.toFun Y.toFun chartBV y := by
    intro y hy
    have hy_chart : y ∈ (chartAt H x).source := by rw [← htriv_base]; exact hy
    have hchartBV_smoothAt : TangentSmoothAt chartBV y := by
      refine TangentSmoothAt.mk ?_
      exact (hchartBV_smooth_on.contMDiffAt
        ((chartAt H x).open_source.mem_nhds hy_chart)).mdifferentiableAt
        (by simp : (∞ : ℕ∞ω) ≠ 0)
    exact TensorialAt.mkHom_apply
      (koszulFunctional_tensorialAt g X.toFun Y.toFun y
        (X.smoothAt y) (Y.smoothAt y)) hchartBV_smoothAt
  have hPhi_chartBV_at : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun y => Φ y (chartBV y)) x := by
    refine hKoszul_chartBV_at_x.congr_of_eventuallyEq ?_
    filter_upwards [hbaseSet_open.mem_nhds hx_base] with y hy
    exact hPhi_eq y hy
  exact hPhi_chartBV_at.contMDiffWithinAt

/-- **Eng.** Constant-direction specialisation of
`koszulCovDeriv_smoothVF_smoothAt` via `SmoothVectorField.const v`. -/
theorem koszulCovDeriv_const_smoothAt
    [IsLocallyConstantChartedSpace H M]
    (g : RiemannianMetric I M)
    (v : E) (Y : SmoothVectorField I M) (x : M) :
    TangentSmoothAt
      (fun y : M => koszulCovDeriv g (fun _ : M => v) Y.toFun y
        ((SmoothVectorField.const (I := I) (M := M) v).smoothAt y)
        (Y.smoothAt y)) x :=
  koszulCovDeriv_smoothVF_smoothAt g (SmoothVectorField.const v) Y x

end Riemannian
