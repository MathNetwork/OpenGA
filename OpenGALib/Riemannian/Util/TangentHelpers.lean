import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.VectorField.LieBracket
import OpenGALib.Riemannian.TangentBundle.TangentSmooth

/-!
# Tangent helpers — chart-bundle smoothness bridges

Engineering scaffolding for the Levi-Civita / Koszul machinery in
`Connection.lean`: chart-pullback bridges that convert between
bundle-section smoothness, function-form `ContMDiff`, and
`TangentSmoothAt` (the framework's MDifferentiableAt predicate). Also
hosts the `SmoothVectorField`-form Jacobi identity wrapping Mathlib's
`leibniz_identity_mlieBracket_apply`.

These helpers depend only on Mathlib's vector-bundle machinery and the
framework's `IsLocallyConstantChartedSpace` / `TangentBundle` API.
-/

open Bundle VectorField
open scoped ContDiff Manifold Topology

namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [IsLocallyConstantChartedSpace H M]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
set_option backward.isDefEq.respectTransparency false in
/-- **Eng.** A `SmoothVectorField`'s underlying `Y.toFun : Π y : M, T_yM`
viewed as `M → E` (via `T_yM = E` def-eq) is globally `ContMDiff` under
`IsLocallyConstantChartedSpace`. Bundle-section ↔ function-form bridge. -/
theorem SmoothVectorField.contMDiff_E (Y : SmoothVectorField I M) :
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
/-- **Eng.** Componentwise lift to continuous linear map-valued: if each component
`(fun y => T y (basis i)) : M → F₂` is `MDifferentiableAt` at `x`, then the
continuous linear map-valued section `T : M → (F₁ →L[ℝ] F₂)` is `MDifferentiableAt` at `x`.
Decomposes `T y = ∑ i (basis.coord i).toContinuousLinearMap.smulRight (T y (basis i))`. -/
theorem mdifferentiableAt_continuousLinearMap_of_components
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
  -- (basis.coord i).toContinuousLinearMap.smulRight : F₂ →L (F₁ →L F₂) is a continuous linear map, hence smooth.
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

/-- **Math.** **Jacobi identity for smooth vector fields**:
$$\bigl[X,\,[Y, Z]\bigr] = \bigl[[X, Y],\,Z\bigr] + \bigl[Y,\,[X, Z]\bigr].$$
Wrapper around Mathlib `VectorField.leibniz_identity_mlieBracket_apply`
taking `SmoothVectorField` inputs, with the `minSmoothness ℝ 2`
downgrade from `∞` handled internally. Stated in raw
`VectorField.mlieBracket` form because this file precedes the
`⟦·,·⟧` notation declaration in `Connection.lean`; consumers can use
the notation when citing.

**Ground truth**: do Carmo §0, Lee Ch. 8. -/
theorem SmoothVectorField.mlieBracket_jacobi
    (X Y Z : SmoothVectorField I M) (x : M) :
    VectorField.mlieBracket I X.toFun
        (VectorField.mlieBracket I Y.toFun Z.toFun) x
      = VectorField.mlieBracket I (VectorField.mlieBracket I X.toFun Y.toFun)
            Z.toFun x
        + VectorField.mlieBracket I Y.toFun
            (VectorField.mlieBracket I X.toFun Z.toFun) x := by
  haveI hM3 : IsManifold I (minSmoothness ℝ 3) M := by
    rw [minSmoothness_of_isRCLikeNormedField]; infer_instance
  have hX_2 : ContMDiffAt I (I.prod 𝓘(ℝ, E)) (minSmoothness ℝ 2)
      (fun y => (⟨y, X.toFun y⟩ : TangentBundle I M)) x := by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact (X.smooth x).of_le (by
      show ((2 : ℕ∞) : ℕ∞ω) ≤ ∞
      exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤))
  have hY_2 : ContMDiffAt I (I.prod 𝓘(ℝ, E)) (minSmoothness ℝ 2)
      (fun y => (⟨y, Y.toFun y⟩ : TangentBundle I M)) x := by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact (Y.smooth x).of_le (by
      show ((2 : ℕ∞) : ℕ∞ω) ≤ ∞
      exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤))
  have hZ_2 : ContMDiffAt I (I.prod 𝓘(ℝ, E)) (minSmoothness ℝ 2)
      (fun y => (⟨y, Z.toFun y⟩ : TangentBundle I M)) x := by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact (Z.smooth x).of_le (by
      show ((2 : ℕ∞) : ℕ∞ω) ≤ ∞
      exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤))
  exact VectorField.leibniz_identity_mlieBracket_apply
    (I := I) (M := M) (U := X.toFun) (V := Y.toFun) (W := Z.toFun)
    hX_2 hY_2 hZ_2

omit [FiniteDimensional ℝ E] [IsLocallyConstantChartedSpace H M] in
/-- **Eng.** `mlieBracket` of two `ContMDiff` bundle sections is `TangentSmoothAt`.
Wrapper around Mathlib `ContMDiffAt.mlieBracket_vectorField` giving the
framework's MDifferentiableAt-form predicate. -/
theorem mlieBracket_tangentSmoothAt
    {U V : (y : M) → TangentSpace I y} {x : M}
    (hU : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (fun y => (⟨y, U y⟩ : TangentBundle I M)))
    (hV : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (fun y => (⟨y, V y⟩ : TangentBundle I M))) :
    TangentSmoothAt (mlieBracket I U V) x := by
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

end Riemannian
