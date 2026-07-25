import DifferentialGeometry.Geometry.Operator.HessianTraceRealization
import DifferentialGeometry.Tensor.RSTensor.Derivation.NablaOnTensors
import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Analysis.Calculus.DerivativeTest

set_option autoImplicit false
set_option linter.style.longLine false












namespace DifferentialGeometry.Integral.Connection

noncomputable section

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private instance tangentSpace_finiteDimensional (x : M) :
    FiniteDimensional Real (TangentSpace I x) :=
  inferInstanceAs (FiniteDimensional Real E)



private noncomputable def tangentConstAt (x : M) (v : TangentSpace I x) (p : M) :
    TangentSpace I p :=
  TensorLieDeriv.tangentConstInChart (𝕜 := Real) (I := I) x v p

omit [FiniteDimensional ℝ E] in
@[simp] private theorem tangentConstAt_self (x : M) (v : TangentSpace I x) :
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

omit [FiniteDimensional ℝ E] in
private theorem mdifferentiableAt_tangentConstAt_self
    (x : M) (v : TangentSpace I x) :
    MDiffAt (T% (tangentConstAt (I := I) x v : (p : M) -> TangentSpace I p)) x := by
  unfold tangentConstAt
  exact TensorLieDeriv.mdifferentiableAt_tangentConstInChart_of_mem
    (𝕜 := Real) (I := I) (x₀ := x) (p := x) v
    (mem_baseSet_trivializationAt E (TangentSpace I) x)

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
private theorem extDerivFun_real_eq_mfderiv
    (u : M -> Real) (x : M) (v : TangentSpace I x) :
    extDerivFun (I := I) u x v =
      mfderiv I 𝓘(Real, Real) u x v := by
  simp [extDerivFun, NormedSpace.fromTangentSpace]






private theorem deriv_deriv_nonneg_of_isLocalMin
    {φ : Real -> Real} {t₀ : Real}
    (hmin : IsLocalMin φ t₀)
    (hcont : ContinuousAt φ t₀) :
    0 <= deriv (deriv φ) t₀ := by
  by_contra hnot
  have hneg : deriv (deriv φ) t₀ < 0 := lt_of_not_ge hnot
  have hmax : IsLocalMax φ t₀ :=
    isLocalMax_of_deriv_deriv_neg hneg hmin.deriv_eq_zero hcont
  have hφ_const : φ =ᶠ[nhds t₀] fun _ => φ t₀ := by
    unfold IsLocalMin IsMinFilter at hmin
    unfold IsLocalMax IsMaxFilter at hmax
    filter_upwards [hmin, hmax] with t hle hge
    exact le_antisymm hge hle
  have hderiv_const :
      deriv φ =ᶠ[nhds t₀] fun _ => 0 := by
    filter_upwards [hφ_const.deriv] with t ht
    simpa using ht
  have hzero : deriv (deriv φ) t₀ = 0 := by
    simpa using hderiv_const.deriv_eq
  linarith



omit [FiniteDimensional ℝ E] in
private theorem fderiv_fderiv_apply_self_nonneg_of_isLocalMin_model
    {F : E -> Real} {y : E}
    (hmin : IsLocalMin F y)
    (hF : DifferentiableAt Real F y)
    (hF_near : ∀ᶠ z in nhds y, DifferentiableAt Real F z)
    (v : E) :
    0 <= fderiv Real (fun z : E => fderiv Real F z v) y v := by
  by_cases hD : DifferentiableAt Real (fun z : E => fderiv Real F z v) y
  · let φ : Real -> Real := fun t => F (y + t • v)
    let line : Real -> E := fun t => y + t • v
    have hline_cont : ContinuousAt line 0 := by
      fun_prop
    have hmin_line : IsLocalMin φ 0 := by
      have hmin' : IsLocalMin F (line 0) := by
        simpa [line] using hmin
      simpa [φ, Function.comp_def] using hmin'.comp_continuous hline_cont
    have hcont_line : ContinuousAt φ 0 := by
      have hF0 : ContinuousAt F (line 0) := by
        simpa [line] using hF.continuousAt
      exact hF0.comp hline_cont
    have hnonneg : 0 <= deriv (deriv φ) 0 :=
      deriv_deriv_nonneg_of_isLocalMin hmin_line hcont_line
    have hline_deriv : ∀ t : Real, HasDerivAt line v t := by
      intro t
      simpa [line, one_smul] using ((hasDerivAt_id t).smul_const v).const_add y
    have hF_line_near :
        ∀ᶠ t in nhds (0 : Real), DifferentiableAt Real F (line t) := by
      have hF_near' : ∀ᶠ z in nhds (line 0), DifferentiableAt Real F z := by
        simpa [line] using hF_near
      exact hline_cont hF_near'
    have hderiv_line :
        deriv φ =ᶠ[nhds (0 : Real)]
          fun t : Real => fderiv Real F (line t) v := by
      filter_upwards [hF_line_near] with t ht
      have hφ : HasDerivAt φ (fderiv Real F (line t) v) t := by
        simpa [φ, line, Function.comp_def] using
          ht.hasFDerivAt.comp_hasDerivAt t (hline_deriv t)
      exact hφ.deriv
    have hDline :
        deriv (fun t : Real => fderiv Real F (line t) v) 0 =
          fderiv Real (fun z : E => fderiv Real F z v) y v := by
      have hcomp :
          HasDerivAt
            (fun t : Real => fderiv Real F (line t) v)
            (fderiv Real (fun z : E => fderiv Real F z v) y v) 0 := by
        simpa [line, Function.comp_def] using
          hD.hasFDerivAt.comp_hasDerivAt_of_eq (x := 0)
            (hline_deriv 0) (by simp [line])
      exact hcomp.deriv
    have hsecond :
        deriv (deriv φ) 0 =
          fderiv Real (fun z : E => fderiv Real F z v) y v := by
      calc
        deriv (deriv φ) 0 =
            deriv (fun t : Real => fderiv Real F (line t) v) 0 := by
          exact hderiv_line.deriv_eq
        _ = fderiv Real (fun z : E => fderiv Real F z v) y v := hDline
    simpa [hsecond] using hnonneg
  · rw [fderiv_zero_of_not_differentiableAt hD]
    exact le_rfl

omit [FiniteDimensional ℝ E] in
private theorem writtenInExtChartAt_differentiableAt_of_mdifferentiableAt
    [I.Boundaryless]
    {f : M -> Real} {x p : M} {z : E}
    (hp : p ∈ (chartAt H x).source)
    (hz : z ∈ (extChartAt I x).target)
    (hpz : p = (extChartAt I x).symm z)
    (h : MDifferentiableAt I 𝓘(Real, Real) f p) :
    DifferentiableAt Real (writtenInExtChartAt I 𝓘(Real, Real) x f) z := by
  have hmd_within :
      MDifferentiableWithinAt 𝓘(Real, E) 𝓘(Real, Real)
        (f ∘ (extChartAt I x).symm) (Set.range I)
        (extChartAt I x p) := by
    exact (mdifferentiableAt_iff_source_of_mem_source
      (I := I) (I' := 𝓘(Real, Real)) (x := x) (x' := p) hp).mp h
  have hdiff_within :
      DifferentiableWithinAt Real (writtenInExtChartAt I 𝓘(Real, Real) x f)
        (Set.range I) (extChartAt I x p) := by
    simpa [writtenInExtChartAt] using hmd_within.differentiableWithinAt
  have hrange : Set.range I ∈ nhds z := by
    rw [ModelWithCorners.Boundaryless.range_eq_univ (I := I)]
    exact Filter.univ_mem
  have hpoint : extChartAt I x p = z := by
    rw [hpz]
    exact (extChartAt I x).right_inv hz
  rw [hpoint] at hdiff_within
  exact hdiff_within.differentiableAt hrange

omit [FiniteDimensional ℝ E] in
private theorem extDerivFun_tangentConstAt_eq_fderiv_writtenInExtChartAt
    [I.Boundaryless]
    {f : M -> Real} {x p : M}
    (hp : p ∈ (chartAt H x).source)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f p)
    (v : TangentSpace I x) :
    extDerivFun (I := I) f p (tangentConstAt (I := I) x v p) =
      fderiv Real (writtenInExtChartAt I 𝓘(Real, Real) x f) (extChartAt I x p) v := by
  let z : E := extChartAt I x p
  have hsource : p ∈ (extChartAt I x).source := by
    simpa [extChartAt_source] using hp
  have hz_target : z ∈ (extChartAt I x).target := by
    simpa [z] using (extChartAt I x).map_source hsource
  have hsymm : (extChartAt I x).symm z = p := by
    simpa [z] using (extChartAt I x).left_inv hsource
  have hrange : Set.range I ∈ nhds z := by
    rw [ModelWithCorners.Boundaryless.range_eq_univ (I := I)]
    exact Filter.univ_mem
  have hsymm_mdiff :
      MDifferentiableWithinAt 𝓘(Real, E) I (extChartAt I x).symm
        (Set.range I) z := by
    simpa [z] using mdifferentiableWithinAt_extChartAt_symm (I := I) hz_target
  have hf_univ :
      MDifferentiableWithinAt I 𝓘(Real, Real) f Set.univ
        ((extChartAt I x).symm z) := by
    rw [hsymm]
    exact hf.mdifferentiableWithinAt
  have hmaps :
      Set.range I ⊆ (extChartAt I x).symm ⁻¹' (Set.univ : Set M) := by
    intro y hy
    simp
  have huniq : UniqueMDiffWithinAt 𝓘(Real, E) (Set.range I) z := by
    exact (I.uniqueDiffOn.uniqueDiffWithinAt
      (by exact extChartAt_target_subset_range (I := I) x hz_target)).uniqueMDiffWithinAt
  have hchain :=
    mfderivWithin_comp (I := 𝓘(Real, E)) (I' := I) (I'' := 𝓘(Real, Real))
      (x := z) (g := f) (f := (extChartAt I x).symm)
      hf_univ hsymm_mdiff hmaps huniq
  have hchain_apply :
      fderivWithin Real (writtenInExtChartAt I 𝓘(Real, Real) x f)
          (Set.range I) z v =
        mfderiv I 𝓘(Real, Real) f p
          ((mfderivWithin 𝓘(Real, E) I (extChartAt I x).symm
            (Set.range I) z) v) := by
    have happ := congrArg (fun L => L v) hchain
    rw [mfderivWithin_eq_fderivWithin, mfderivWithin_univ] at happ
    rw [hsymm] at happ
    simpa [writtenInExtChartAt, z, ContinuousLinearMap.comp_apply] using happ
  have hfield :
      tangentConstAt (I := I) x v p =
        (mfderivWithin 𝓘(Real, E) I (extChartAt I x).symm
          (Set.range I) z) v := by
    have hlin := TangentBundle.symmL_trivializationAt
      (𝕜 := Real) (I := I) (x₀ := x) (x := p) hp
    have happ := congrArg (fun L => L v) hlin
    simpa [tangentConstAt, z] using happ
  have hwithin_to_fderiv :
      fderivWithin Real (writtenInExtChartAt I 𝓘(Real, Real) x f)
          (Set.range I) z v =
        fderiv Real (writtenInExtChartAt I 𝓘(Real, Real) x f) z v := by
    rw [fderivWithin_of_mem_nhds hrange]
  rw [extDerivFun_real_eq_mfderiv, hfield]
  exact hchain_apply.symm.trans hwithin_to_fderiv








omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem mfderiv_eq_zero_at_spatial_min
    [I.Boundaryless]
    {f : M -> Real} {x : M}
    (hmin : IsLocalMin f x)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x) :
    mfderiv I 𝓘(Real, Real) f x = 0 := by
  have hmin_chart :
      IsLocalMin (fun y : E => f ((extChartAt I x).symm y))
        ((extChartAt I x) x) := by
    have hmin' :
        IsLocalMin f ((extChartAt I x).symm ((extChartAt I x) x)) := by
      simpa only [mfld_simps] using hmin
    simpa only [Function.comp_apply] using
      hmin'.comp_continuous (continuousAt_extChartAt_symm (I := I) x)
  have hderiv_chart :
      fderiv Real (fun y : E => f ((extChartAt I x).symm y))
        ((extChartAt I x) x) = 0 :=
    hmin_chart.fderiv_eq_zero
  have hrange : Set.range I ∈ nhds ((extChartAt I x) x) := by
    rw [ModelWithCorners.Boundaryless.range_eq_univ (I := I)]
    exact Filter.univ_mem
  calc
    mfderiv I 𝓘(Real, Real) f x =
        fderivWithin Real (writtenInExtChartAt I 𝓘(Real, Real) x f)
          (Set.range I) ((extChartAt I x) x) := by
      exact hf.mfderiv
    _ = fderiv Real (writtenInExtChartAt I 𝓘(Real, Real) x f)
          ((extChartAt I x) x) := by
      exact fderivWithin_of_mem_nhds hrange
    _ = 0 := by
      simpa [writtenInExtChartAt] using hderiv_chart


theorem gradientFun_eq_zero_at_spatial_min
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) {f : M -> Real} {x : M}
    (hmin : IsLocalMin f x)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x) :
    gradientFun (I := I) g f x = 0 := by
  exact gradientFun_eq_zero_of_mfderiv_eq_zero (I := I) g f
    (mfderiv_eq_zero_at_spatial_min (I := I) hmin hf)




def LaplacianNonnegativeAtSpatialMin
    [I.Boundaryless]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M) : Prop :=
  forall {f : M -> Real} {x : M},
    IsLocalMin f x ->
      MDifferentiableAt I 𝓘(Real, Real) f x ->
        (∀ᶠ y in nhds x, MDifferentiableAt I 𝓘(Real, Real) f y) ->
        MDiffAt (T% fun y : M => gradientFun (I := I) g f y) x ->
          0 <= laplacian (I := I) cov g f x



theorem divergence_eq_of_section_eq_zero
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    (cov cov' : CovariantDerivative I E (TangentSpace I : M -> Type _))
    {X : (x : M) -> TangentSpace I x} {x : M}
    (hX : MDiffAt (T% X) x) (hzero : X x = 0) :
    divergence (I := I) cov X x = divergence (I := I) cov' X x := by
  have hd :
      (CovariantDerivative.difference cov cov' x) (X x) =
        cov X x - cov' X x := by
    exact IsCovariantDerivativeOn.difference_apply
      (hcov := cov.isCovariantDerivativeOnUniv)
      (hcov' := cov'.isCovariantDerivativeOnUniv)
      (σ := X) (x := x) (hx := by trivial) hX
  have hcov_eq : cov X x = cov' X x := by
    have hsub : cov X x - cov' X x = 0 := by
      rw [← hd, hzero]
      simp
    exact sub_eq_zero.mp hsub
  simp [divergence, hcov_eq]



theorem laplacian_eq_laplacian_of_gradient_eq_zero
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    (cov cov' : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M) {f : M -> Real} {x : M}
    (hgradSec : MDiffAt (T% fun y : M => gradientFun (I := I) g f y) x)
    (hgrad : gradientFun (I := I) g f x = 0) :
    laplacian (I := I) cov g f x = laplacian (I := I) cov' g f x := by
  exact divergence_eq_of_section_eq_zero (I := I) cov cov' hgradSec hgrad








private theorem fderiv_fderiv_self_nonneg_of_isLocalMin
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M -> Real} {x : M}
    (hmin : IsLocalMin f x)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hf_near : ∀ᶠ y in nhds x, MDifferentiableAt I 𝓘(Real, Real) f y)
    (_hgrad : MDiffAt (T% fun y : M => gradientFun (I := I) g f y) x)
    (v : TangentSpace I x) :
    0 <=
      extDerivFun (I := I)
        (fun y : M =>
          extDerivFun (I := I) f y
            (tangentConstAt (I := I) x v y)) x v := by
  let F : E -> Real := writtenInExtChartAt I 𝓘(Real, Real) x f
  let z₀ : E := extChartAt I x x
  have hmin_chart : IsLocalMin F z₀ := by
    have hmin' :
        IsLocalMin f ((extChartAt I x).symm ((extChartAt I x) x)) := by
      simpa only [mfld_simps] using hmin
    simpa [F, z₀, writtenInExtChartAt, Function.comp_def] using
      hmin'.comp_continuous (continuousAt_extChartAt_symm (I := I) x)
  have hF : DifferentiableAt Real F z₀ := by
    exact writtenInExtChartAt_differentiableAt_of_mdifferentiableAt
      (I := I) (x := x) (p := x) (z := z₀)
      (mem_chart_source H x) (by simp [z₀])
      (by simp [z₀]) hf
  have hsymm_tend :
      Filter.Tendsto (fun z : E => (extChartAt I x).symm z) (nhds z₀) (nhds x) := by
    have hleft : (extChartAt I x).symm ((extChartAt I x) x) = x :=
      (extChartAt I x).left_inv (mem_extChartAt_source (I := I) x)
    simpa only [ContinuousAt, z₀, hleft, Function.comp_def] using
      continuousAt_extChartAt_symm (I := I) x
  have hF_near_model : ∀ᶠ z in nhds z₀, DifferentiableAt Real F z := by
    have hmd_z :
        ∀ᶠ z in nhds z₀,
          MDifferentiableAt I 𝓘(Real, Real) f ((extChartAt I x).symm z) :=
      hsymm_tend hf_near
    have hsource_z :
        ∀ᶠ z in nhds z₀, (extChartAt I x).symm z ∈ (chartAt H x).source :=
      hsymm_tend ((chartAt H x).open_source.mem_nhds (mem_chart_source H x))
    have htarget_z :
        ∀ᶠ z in nhds z₀, z ∈ (extChartAt I x).target :=
      extChartAt_target_mem_nhds' (I := I)
        (by simp [z₀])
    filter_upwards [hmd_z, hsource_z, htarget_z] with z hmd hsource htarget
    exact writtenInExtChartAt_differentiableAt_of_mdifferentiableAt
      (I := I) (x := x) (p := (extChartAt I x).symm z) (z := z)
      hsource htarget rfl hmd
  have hmodel :=
    fderiv_fderiv_apply_self_nonneg_of_isLocalMin_model
      (F := F) (y := z₀) hmin_chart hF hF_near_model v
  let u : M -> Real :=
    fun y : M =>
      extDerivFun (I := I) f y
        (tangentConstAt (I := I) x v y)
  have hwrite_eq :
      writtenInExtChartAt I 𝓘(Real, Real) x u =ᶠ[nhds z₀]
        fun z : E => fderiv Real F z v := by
    have hmd_z :
        ∀ᶠ z in nhds z₀,
          MDifferentiableAt I 𝓘(Real, Real) f ((extChartAt I x).symm z) :=
      hsymm_tend hf_near
    have hsource_z :
        ∀ᶠ z in nhds z₀, (extChartAt I x).symm z ∈ (chartAt H x).source :=
      hsymm_tend ((chartAt H x).open_source.mem_nhds (mem_chart_source H x))
    have htarget_z :
        ∀ᶠ z in nhds z₀, z ∈ (extChartAt I x).target :=
      extChartAt_target_mem_nhds' (I := I)
        (by simp [z₀])
    filter_upwards [hmd_z, hsource_z, htarget_z] with z hmd hsource htarget
    have h :=
      extDerivFun_tangentConstAt_eq_fderiv_writtenInExtChartAt
        (I := I) (x := x) (p := (extChartAt I x).symm z)
        hsource hmd v
    have hright : extChartAt I x ((extChartAt I x).symm z) = z :=
      (extChartAt I x).right_inv htarget
    change
      mfderiv I 𝓘(Real, Real) f ((extChartAt I x).symm z)
          (tangentConstAt (I := I) x v ((extChartAt I x).symm z)) =
        fderiv Real F (extChartAt I x ((extChartAt I x).symm z)) v at h
    rw [hright] at h
    simpa [u, writtenInExtChartAt, extDerivFun, NormedSpace.fromTangentSpace,
      ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.coe_mk, LinearEquiv.coe_mk] using h
  change 0 <= extDerivFun (I := I) u x v
  by_cases hu : MDifferentiableAt I 𝓘(Real, Real) u x
  · have hrange : Set.range I ∈ nhds z₀ := by
      rw [ModelWithCorners.Boundaryless.range_eq_univ (I := I)]
      exact Filter.univ_mem
    have houter :
        extDerivFun (I := I) u x v =
          fderiv Real (writtenInExtChartAt I 𝓘(Real, Real) x u) z₀ v := by
      rw [extDerivFun_real_eq_mfderiv]
      calc
        mfderiv I 𝓘(Real, Real) u x v =
            fderivWithin Real (writtenInExtChartAt I 𝓘(Real, Real) x u)
              (Set.range I) z₀ v := by
          simpa [z₀] using congrArg (fun L => L v) hu.mfderiv
        _ = fderiv Real (writtenInExtChartAt I 𝓘(Real, Real) x u) z₀ v := by
          rw [fderivWithin_of_mem_nhds hrange]
    have hrewrite :
        fderiv Real (writtenInExtChartAt I 𝓘(Real, Real) x u) z₀ v =
          fderiv Real (fun z : E => fderiv Real F z v) z₀ v := by
      rw [hwrite_eq.fderiv_eq]
    calc
      0 <= fderiv Real (fun z : E => fderiv Real F z v) z₀ v := hmodel
      _ = extDerivFun (I := I) u x v := by
        rw [← hrewrite, ← houter]
  · rw [extDerivFun_real_eq_mfderiv]
    rw [mfderiv, if_neg hu]
    exact le_rfl



private theorem cov_gradient_inner_self_nonneg_at_spatial_min
    [I.Boundaryless]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    (hmc : DifferentialGeometry.Integral.Connection.IsMetricCompatible_gen (I := I) cov g)
    {f : M -> Real} {x : M}
    (hmin : IsLocalMin f x)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hf_near : ∀ᶠ y in nhds x, MDifferentiableAt I 𝓘(Real, Real) f y)
    (hgrad : MDiffAt (T% fun y : M => gradientFun (I := I) g f y) x)
    (v : TangentSpace I x) :
    0 <=
      g.inner x
        ((cov (fun y : M => gradientFun (I := I) g f y) x) v) v := by
  let V : (p : M) -> TangentSpace I p := tangentConstAt (I := I) x v
  let G : (p : M) -> TangentSpace I p := fun y : M => gradientFun (I := I) g f y
  have hV : MDiffAt (T% V) x := by
    simpa [V] using mdifferentiableAt_tangentConstAt_self (I := I) x v
  have hcritical : G x = 0 := by
    simpa [G] using gradientFun_eq_zero_at_spatial_min (I := I) g hmin hf
  have hmetric := DifferentialGeometry.Integral.Connection.metric_compatible_apply
    (I := I) hmc V G V hV hgrad hV
  have hfun :
      (fun y : M => g.inner y (G y) (V y)) =
        fun y : M =>
          extDerivFun (I := I) f y
            (tangentConstAt (I := I) x v y) := by
    funext y
    rw [extDerivFun_real_eq_mfderiv]
    simpa [G, V] using inner_gradientFun (I := I) g f y (V y)
  have hmetric' :
      extDerivFun (I := I)
          (fun y : M =>
            extDerivFun (I := I) f y
              (tangentConstAt (I := I) x v y)) x v =
        g.inner x
          ((cov (fun y : M => gradientFun (I := I) g f y) x) v) v := by
    rw [← hfun]
    rw [extDerivFun_real_eq_mfderiv]
    have hVx : V x = v := by
      simp [V, tangentConstAt_self]
    rw [hVx] at hmetric
    have hzero :
        g.inner x (G x) ((cov V x) v) = 0 := by
      rw [hcritical]
      simp
    rw [hzero, add_zero] at hmetric
    simpa [G, V] using hmetric
  rw [← hmetric']
  exact fderiv_fderiv_self_nonneg_of_isLocalMin (I := I) g hmin hf hf_near hgrad v



theorem laplacian_nonneg_at_spatial_min_of_metricCompatible
    [I.Boundaryless]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    (hmc : DifferentialGeometry.Integral.Connection.IsMetricCompatible_gen (I := I) cov g)
    {f : M -> Real} {x : M}
    (hmin : IsLocalMin f x)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hf_near : ∀ᶠ y in nhds x, MDifferentiableAt I 𝓘(Real, Real) f y)
    (hgrad : MDiffAt (T% fun y : M => gradientFun (I := I) g f y) x) :
  0 <= laplacian (I := I) cov g f x := by
  unfold laplacian divergence
  exact Tensor0SBundle.linearMap_trace_nonneg_of_metric_inner_apply_self_nonneg
    (I := I) g x
    ((cov (fun y : M => gradientFun (I := I) g f y) x).toLinearMap)
    (fun v => by
      simpa using
        cov_gradient_inner_self_nonneg_at_spatial_min
          (I := I) cov g hmc hmin hf hf_near hgrad v)


theorem laplacianNonnegativeAtSpatialMin_of_metricCompatible
    [I.Boundaryless]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    (hmc : DifferentialGeometry.Integral.Connection.IsMetricCompatible_gen (I := I) cov g) :
    LaplacianNonnegativeAtSpatialMin (I := I) cov g := by
  intro f x hmin hf hf_near hgrad
  exact laplacian_nonneg_at_spatial_min_of_metricCompatible
    (I := I) cov g hmc hmin hf hf_near hgrad

end

end DifferentialGeometry.Integral.Connection
