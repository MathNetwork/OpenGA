import DifferentialGeometry.Geometry.Boundary.BoundaryManifold
import DifferentialGeometry.Analysis.Integration.Measure.ChartDensity
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.Bounded


noncomputable section

open Set Function Topology Bundle Manifold MeasureTheory Bornology
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry
namespace Integral
namespace DivergenceTheorem
namespace WithBoundary

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

def boundaryInclusion (I : ModelWithCorners ℝ E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] :
    BoundaryManifold I M → M :=
  Subtype.val

omit [FiniteDimensional ℝ E] in
@[simp] lemma boundaryInclusion_apply (x : BoundaryManifold I M) :
    boundaryInclusion I M x = (x : M) := rfl

private def Phi (I : ModelWithCorners ℝ E H) [hI : HasSmoothBoundary E H I] :
    hI.boundaryE → E :=
  (I : H → E) ∘ hI.inclH ∘ hI.boundaryI.symm

omit [FiniteDimensional ℝ E] in
private lemma Phi_eq (I : ModelWithCorners ℝ E H) [hI : HasSmoothBoundary E H I] :
    Phi I = (I : H → E) ∘ hI.inclH ∘ hI.boundaryI.symm := rfl

omit [FiniteDimensional ℝ E] in
private lemma Phi_contDiff (I : ModelWithCorners ℝ E H)
    [hI : HasSmoothBoundary E H I] :
    ContDiff ℝ ∞ (Phi I) :=
  hI.I_inclH_boundaryI_symm_contDiff

omit [FiniteDimensional ℝ E] in
private lemma projE_comp_Phi (I : ModelWithCorners ℝ E H)
    [hI : HasSmoothBoundary E H I] :
    hI.projE ∘ Phi I = id := by
  funext e
  have h1 : hI.projE (I (hI.inclH (hI.boundaryI.symm e)))
      = hI.boundaryI (hI.boundaryI.symm e) :=
    hI.proj_inclH_compat (hI.boundaryI.symm e)
  have h2 : hI.boundaryI (hI.boundaryI.symm e) = e := by
    have hmem : e ∈ Set.range hI.boundaryI := by
      rw [hI.boundaryI.range_eq_univ]; exact Set.mem_univ _
    rcases hmem with ⟨b, rfl⟩
    rw [hI.boundaryI.left_inv b]
  change hI.projE (Phi I e) = e
  rw [Phi_eq]
  simpa [Function.comp] using h1.trans h2

private lemma infty_ne_zero_withTopENat : (∞ : WithTop ℕ∞) ≠ 0 := by
  intro h
  have h' : ((⊤ : ℕ∞) : WithTop ℕ∞) = ((0 : ℕ∞) : WithTop ℕ∞) := h
  exact ENat.top_ne_zero (WithTop.coe_eq_coe.mp h')

omit [FiniteDimensional ℝ E] in
theorem boundaryInclusion_contMDiff
    [hI : HasSmoothBoundary E H I] [IsManifold I ∞ M] :
    ContMDiff hI.boundaryI I ∞ (boundaryInclusion I M) := by
  refine contMDiff_of_locally_contMDiffOn ?_
  intro x
  by_cases hN : Nonempty hI.boundaryH
  · haveI := hN
    refine ⟨BoundaryManifold.boundaryChartSource (I := I) x,
      BoundaryManifold.isOpen_boundaryChartSource (I := I) x,
      BoundaryManifold.mem_boundaryChartSource_self (I := I) x, ?_⟩
    have h_chart_eq : chartAt hI.boundaryH x = BoundaryManifold.boundaryChart (I := I) x := by
      change BoundaryManifold.defaultBoundaryChart (I := I) x =
        BoundaryManifold.boundaryChart (I := I) x
      exact BoundaryManifold.defaultBoundaryChart_eq_boundaryChart (I := I) x
    have hs : BoundaryManifold.boundaryChartSource (I := I) x ⊆
        (chartAt hI.boundaryH x).source := by
      intro y hy
      rw [h_chart_eq]
      change y ∈ BoundaryManifold.boundaryChartSource (I := I) x
      exact hy
    have h2s : MapsTo (boundaryInclusion I M)
        (BoundaryManifold.boundaryChartSource (I := I) x)
        (chartAt H ((boundaryInclusion I M x : M))).source := by
      intro y hy
      change (y : M) ∈ (chartAt H (x : M)).source at hy
      change (y : M) ∈ (chartAt H ((x : M))).source
      exact hy
    rw [contMDiffOn_iff_of_subset_source (x := x) (y := (x : M)) hs h2s]
    refine ⟨continuous_subtype_val.continuousOn, ?_⟩
    have hPhi : ContDiff ℝ ∞ (Phi I) := Phi_contDiff I
    refine hPhi.contDiffOn.congr ?_
    intro e he
    rcases he with ⟨y, hy_src, hy_eq⟩
    change (y : M) ∈ (chartAt H (x : M)).source at hy_src
    change (extChartAt I (boundaryInclusion I M x) ∘ boundaryInclusion I M ∘
      (extChartAt hI.boundaryI x).symm) e = Phi I e
    simp only [Function.comp_apply]
    have h_e_eq :
        e = hI.boundaryI (BoundaryManifold.boundaryChart (I := I) x y) := by
      rw [← hy_eq]
      change hI.boundaryI (chartAt hI.boundaryH x y) =
        hI.boundaryI (BoundaryManifold.boundaryChart (I := I) x y)
      rw [h_chart_eq]
    have h_y_in_source :
        y ∈ (BoundaryManifold.boundaryChart (I := I) x).source := hy_src
    have h_inv : (extChartAt hI.boundaryI x).symm e = y := by
      rw [h_e_eq]
      change (chartAt hI.boundaryH x).symm
          (hI.boundaryI.symm (hI.boundaryI
            (BoundaryManifold.boundaryChart (I := I) x y))) = y
      rw [hI.boundaryI.left_inv]
      rw [h_chart_eq]
      exact (BoundaryManifold.boundaryChart (I := I) x).left_inv h_y_in_source
    rw [h_inv]
    have hinclH := BoundaryManifold.inclH_boundaryChart_apply
      (I := I) x y hy_src
    change I (chartAt H (x : M) (y : M)) = Phi I e
    rw [h_e_eq, Phi_eq]
    simp only [Function.comp_apply]
    rw [hI.boundaryI.left_inv]
    rw [hinclH]
  · haveI : IsEmpty hI.boundaryH := not_nonempty_iff.mp hN
    haveI : IsEmpty (BoundaryManifold I M) :=
      BoundaryManifold.isEmpty_of_isEmpty_boundaryH (I := I)
    exact (IsEmpty.false x).elim

variable [hI : HasSmoothBoundary E H I] [IsManifold I ∞ M]

noncomputable def boundaryInclusionMfderiv (x : BoundaryManifold I M) :
    hI.boundaryE →L[ℝ] E :=
  mfderiv hI.boundaryI I (boundaryInclusion I M) x

omit [FiniteDimensional ℝ E] in
@[simp] lemma dincl_eq (x : BoundaryManifold I M) :
    (boundaryInclusionMfderiv x : hI.boundaryE →L[ℝ] E) =
      mfderiv hI.boundaryI I (boundaryInclusion I M) x := rfl

omit [FiniteDimensional ℝ E] in
private lemma boundaryInclusion_mdifferentiableAt (x : BoundaryManifold I M) :
    MDifferentiableAt hI.boundaryI I (boundaryInclusion I M) x :=
  (boundaryInclusion_contMDiff (I := I) (M := M)).mdifferentiableAt
    infty_ne_zero_withTopENat

omit [FiniteDimensional ℝ E] in
private lemma dincl_eq_fderiv_Phi (x : BoundaryManifold I M)
    [Nonempty hI.boundaryH] :
    (boundaryInclusionMfderiv x : hI.boundaryE →L[ℝ] E) =
      fderiv ℝ (Phi I) (extChartAt hI.boundaryI x x) := by
  unfold boundaryInclusionMfderiv
  rw [(boundaryInclusion_mdifferentiableAt (I := I) (M := M) x).mfderiv]
  have h_range : Set.range hI.boundaryI = Set.univ := hI.boundaryI.range_eq_univ
  rw [h_range, fderivWithin_univ]
  have h_chart_eq : chartAt hI.boundaryH x = BoundaryManifold.boundaryChart (I := I) x := by
    change BoundaryManifold.defaultBoundaryChart (I := I) x =
      BoundaryManifold.boundaryChart (I := I) x
    exact BoundaryManifold.defaultBoundaryChart_eq_boundaryChart (I := I) x
  have h_eq : (writtenInExtChartAt hI.boundaryI I x (boundaryInclusion I M))
      =ᶠ[𝓝 (extChartAt hI.boundaryI x x)] Phi I := by
    have h_target_mem : (extChartAt hI.boundaryI x).target ∈
        𝓝 (extChartAt hI.boundaryI x x) :=
      extChartAt_target_mem_nhds (I := hI.boundaryI) (M := BoundaryManifold I M) x
    filter_upwards [h_target_mem] with e he
    have he_target_chart : hI.boundaryI.symm e ∈ (chartAt hI.boundaryH x).target := by
      rw [extChartAt_target] at he
      exact he.1
    rw [h_chart_eq] at he_target_chart
    have h_extChart_symm_val :
        (((extChartAt hI.boundaryI x).symm e : BoundaryManifold I M) : M) =
          (chartAt H (x : M)).symm (hI.inclH (hI.boundaryI.symm e)) := by
      change (((chartAt hI.boundaryH x).symm (hI.boundaryI.symm e) :
          BoundaryManifold I M) : M) = _
      rw [h_chart_eq]
      exact BoundaryManifold.boundaryChartInvFun_val_of_mem_target
        (I := I) x he_target_chart
    change writtenInExtChartAt hI.boundaryI I x (boundaryInclusion I M) e = Phi I e
    unfold writtenInExtChartAt
    simp only [Function.comp_apply]
    change extChartAt I (boundaryInclusion I M x)
        (((extChartAt hI.boundaryI x).symm e : BoundaryManifold I M) : M) = Phi I e
    rw [h_extChart_symm_val]
    change I (chartAt H (x : M) ((chartAt H (x : M)).symm
      (hI.inclH (hI.boundaryI.symm e)))) = Phi I e
    rw [(chartAt H (x : M)).right_inv he_target_chart]
    rfl
  rw [Filter.EventuallyEq.fderiv_eq h_eq]

omit [FiniteDimensional ℝ E] in
private lemma fderiv_Phi_injective (e : hI.boundaryE) :
    Function.Injective (fderiv ℝ (Phi I) e) := by
  have h_proj_phi : hI.projE ∘ Phi I = id := projE_comp_Phi I
  have hPhi : ContDiff ℝ ∞ (Phi I) := Phi_contDiff I
  have hproj : ContDiff ℝ ∞ hI.projE := hI.projE_contDiff
  have hPhi_diff : Differentiable ℝ (Phi I) := hPhi.differentiable (by simp)
  have hproj_diff : Differentiable ℝ hI.projE := hproj.differentiable (by simp)
  have h_chain : fderiv ℝ (hI.projE ∘ Phi I) e =
      (fderiv ℝ hI.projE (Phi I e)).comp (fderiv ℝ (Phi I) e) :=
    fderiv_comp e (hproj_diff (Phi I e)) (hPhi_diff e)
  have h_id_eq : fderiv ℝ (hI.projE ∘ Phi I) e =
      ContinuousLinearMap.id ℝ hI.boundaryE := by
    rw [h_proj_phi]; exact fderiv_id
  have h_comp_id : (fderiv ℝ hI.projE (Phi I e)).comp (fderiv ℝ (Phi I) e) =
      ContinuousLinearMap.id ℝ hI.boundaryE := by
    rw [← h_chain, h_id_eq]
  intro v w hvw
  have h_apply :
      (fderiv ℝ hI.projE (Phi I e)).comp (fderiv ℝ (Phi I) e) v =
      (fderiv ℝ hI.projE (Phi I e)).comp (fderiv ℝ (Phi I) e) w := by
    simp [hvw]
  rw [h_comp_id] at h_apply
  simpa using h_apply

omit [FiniteDimensional ℝ E] in
lemma dincl_injective (x : BoundaryManifold I M) :
    Function.Injective (boundaryInclusionMfderiv x) := by
  by_cases hN : Nonempty hI.boundaryH
  · haveI := hN
    rw [dincl_eq_fderiv_Phi (I := I) (M := M) x]
    exact fderiv_Phi_injective (extChartAt hI.boundaryI x x)
  · haveI : IsEmpty hI.boundaryH := not_nonempty_iff.mp hN
    haveI : IsEmpty (BoundaryManifold I M) :=
      BoundaryManifold.isEmpty_of_isEmpty_boundaryH (I := I)
    exact (IsEmpty.false x).elim

private noncomputable def innerOnE
    (g : Measure.SmoothRiemannianMetric I M) (y : M) :
    E →L[ℝ] E →L[ℝ] ℝ := g.inner y

omit [FiniteDimensional ℝ E] hI in
@[simp] private lemma innerOnE_apply
    (g : Measure.SmoothRiemannianMetric I M) (y : M) (u v : E) :
    innerOnE g y u v = g.inner y u v := rfl

noncomputable def inducedMetricInner
    (g : Measure.SmoothRiemannianMetric I M) (x : BoundaryManifold I M) :
    hI.boundaryE →L[ℝ] hI.boundaryE →L[ℝ] ℝ :=
  (innerOnE g (x : M)).bilinearComp (boundaryInclusionMfderiv x) (boundaryInclusionMfderiv x)

omit [FiniteDimensional ℝ E] in
@[simp] lemma inducedMetricInner_apply
    (g : Measure.SmoothRiemannianMetric I M) (x : BoundaryManifold I M)
    (v w : hI.boundaryE) :
    inducedMetricInner g x v w = g.inner (x : M) (boundaryInclusionMfderiv x v) (boundaryInclusionMfderiv x w) :=
  ContinuousLinearMap.bilinearComp_apply _ _ _ _ _

omit [FiniteDimensional ℝ E] in
lemma inducedMetricInner_symm
    (g : Measure.SmoothRiemannianMetric I M) (x : BoundaryManifold I M)
    (v w : hI.boundaryE) :
    inducedMetricInner g x v w = inducedMetricInner g x w v := by
  rw [inducedMetricInner_apply, inducedMetricInner_apply]
  exact g.symm (x : M) (boundaryInclusionMfderiv x v) (boundaryInclusionMfderiv x w)

omit [FiniteDimensional ℝ E] in
lemma inducedMetricInner_pos
    (g : Measure.SmoothRiemannianMetric I M) (x : BoundaryManifold I M)
    (v : hI.boundaryE) (hv : v ≠ 0) :
    0 < inducedMetricInner g x v v := by
  rw [inducedMetricInner_apply]
  apply g.pos (x : M) (boundaryInclusionMfderiv x v)
  intro h0
  apply hv
  have h_zero : (boundaryInclusionMfderiv x) (0 : hI.boundaryE) = 0 := map_zero _
  exact dincl_injective (I := I) (M := M) x (h0.trans h_zero.symm)

private lemma exists_coercive_of_posDef
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hpos : ∀ v : V, v ≠ 0 → 0 < B v v) :
    ∃ c : ℝ, 0 < c ∧ ∀ v : V, c * (‖v‖ * ‖v‖) ≤ B v v := by
  classical
  by_cases hzero : ∀ v : V, v = 0
  · refine ⟨1, by norm_num, ?_⟩
    intro v
    rw [hzero v]; simp
  push Not at hzero
  obtain ⟨v₀, hv₀⟩ := hzero
  let S : Set V := {v | ‖v‖ = 1}
  have hS_eq : S = (Metric.closedBall (0 : V) 1) ∩ {v | ‖v‖ = 1} := by
    ext v
    refine ⟨fun h => ⟨?_, h⟩, fun h => h.2⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    exact h.le
  have hS_compact : IsCompact S := by
    rw [hS_eq]
    refine IsCompact.inter_right (isCompact_closedBall (0 : V) 1) ?_
    exact isClosed_eq continuous_norm continuous_const
  have hv₀_norm_pos : 0 < ‖v₀‖ := norm_pos_iff.mpr hv₀
  have hS_nonempty : S.Nonempty := by
    refine ⟨(‖v₀‖)⁻¹ • v₀, ?_⟩
    change ‖(‖v₀‖)⁻¹ • v₀‖ = 1
    rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_norm]
    field_simp
  have h_cont : Continuous (fun v : V => B v v) :=
    (B.continuous.clm_apply continuous_id)
  obtain ⟨v₁, hv₁_mem, hv₁_min⟩ := hS_compact.exists_isMinOn hS_nonempty h_cont.continuousOn
  have h_norm₁ : ‖v₁‖ = 1 := hv₁_mem
  have h_v₁_ne : v₁ ≠ 0 := by
    intro h0; rw [h0, norm_zero] at h_norm₁; exact zero_ne_one h_norm₁
  set c : ℝ := B v₁ v₁
  have hc_pos : 0 < c := hpos v₁ h_v₁_ne
  refine ⟨c, hc_pos, ?_⟩
  intro v
  by_cases hvz : v = 0
  · simp [hvz]
  · have hnorm_v_pos : 0 < ‖v‖ := norm_pos_iff.mpr hvz
    set u : V := (‖v‖)⁻¹ • v with hu_def
    have h_u_norm : ‖u‖ = 1 := by
      change ‖(‖v‖)⁻¹ • v‖ = 1
      rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_norm]
      field_simp
    have h_u_min : c ≤ B u u := hv₁_min h_u_norm
    have h_B_u : B u u = (‖v‖)⁻¹ * ((‖v‖)⁻¹ * B v v) := by
      change B ((‖v‖)⁻¹ • v) ((‖v‖)⁻¹ • v) = (‖v‖)⁻¹ * ((‖v‖)⁻¹ * B v v)
      have h1 : B ((‖v‖)⁻¹ • v) = (‖v‖)⁻¹ • B v := map_smul B _ _
      rw [h1]
      simp [ContinuousLinearMap.smul_apply, smul_eq_mul, map_smul]
    have h_v_sq_pos : 0 ≤ ‖v‖ * ‖v‖ := mul_nonneg (le_of_lt hnorm_v_pos) (le_of_lt hnorm_v_pos)
    have h_ne : ‖v‖ ≠ 0 := ne_of_gt hnorm_v_pos
    have h_simplify : B u u * (‖v‖ * ‖v‖) = B v v := by
      rw [h_B_u]
      field_simp
    have h_step : c * (‖v‖ * ‖v‖) ≤ B u u * (‖v‖ * ‖v‖) :=
      mul_le_mul_of_nonneg_right h_u_min h_v_sq_pos
    rw [h_simplify] at h_step
    exact h_step

omit [FiniteDimensional ℝ E] in
lemma inducedMetricInner_isVonNBounded
    (g : Measure.SmoothRiemannianMetric I M) (x : BoundaryManifold I M) :
    IsVonNBounded ℝ {v : hI.boundaryE | inducedMetricInner g x v v < 1} := by
  obtain ⟨c, hc_pos, hc_bound⟩ := exists_coercive_of_posDef
    (V := hI.boundaryE) (inducedMetricInner g x)
    (fun v hv => inducedMetricInner_pos (I := I) (M := M) g x v hv)
  rw [NormedSpace.isVonNBounded_iff' (𝕜 := ℝ)]
  refine ⟨Real.sqrt (1 / c), ?_⟩
  intro v hv
  change ‖v‖ ≤ Real.sqrt (1 / c)
  have h_lt : c * (‖v‖ * ‖v‖) < 1 := lt_of_le_of_lt (hc_bound v) hv
  have h_v_sq_lt : ‖v‖ * ‖v‖ < 1 / c := by
    rw [lt_div_iff₀ hc_pos]; rw [mul_comm] at h_lt; exact h_lt
  have h_v_sq_le : ‖v‖ * ‖v‖ ≤ 1 / c := le_of_lt h_v_sq_lt
  have h_norm_nn : 0 ≤ ‖v‖ := norm_nonneg v
  calc ‖v‖ = Real.sqrt (‖v‖ * ‖v‖) := by
            rw [show ‖v‖ * ‖v‖ = ‖v‖^2 from (sq ‖v‖).symm,
              Real.sqrt_sq h_norm_nn]
    _ ≤ Real.sqrt (1 / c) := Real.sqrt_le_sqrt h_v_sq_le

private noncomputable def inducedMetricInnerLocal
    (g : Measure.SmoothRiemannianMetric I M) (x₀ : BoundaryManifold I M) :
    hI.boundaryE → (hI.boundaryE →L[ℝ] hI.boundaryE →L[ℝ] ℝ) :=
  fun e =>
    (innerOnE g ((extChartAt I (x₀ : M)).symm (Phi I e))).bilinearComp
      (fderiv ℝ (Phi I) e) (fderiv ℝ (Phi I) e)

omit [FiniteDimensional ℝ E] in
@[simp] private lemma inducedMetricInnerLocal_apply
    (g : Measure.SmoothRiemannianMetric I M) (x₀ : BoundaryManifold I M)
    (e : hI.boundaryE) (v w : hI.boundaryE) :
    inducedMetricInnerLocal (I := I) (M := M) g x₀ e v w =
      g.inner ((extChartAt I (x₀ : M)).symm (Phi I e))
        (fderiv ℝ (Phi I) e v) (fderiv ℝ (Phi I) e w) := by
  change (innerOnE g _).bilinearComp _ _ v w = _
  exact ContinuousLinearMap.bilinearComp_apply _ _ _ _ _

omit [FiniteDimensional ℝ E] in
private lemma fderiv_Phi_contDiff :
    ContDiff ℝ ∞ (fun e : hI.boundaryE => fderiv ℝ (Phi I) e) :=
  (Phi_contDiff I).fderiv_right (m := ∞) le_rfl

private lemma bilinearComp_smooth_at
    {Eb Hb Bb : Type*} [NormedAddCommGroup Eb] [NormedSpace ℝ Eb]
    [TopologicalSpace Hb] {Ib : ModelWithCorners ℝ Eb Hb}
    [TopologicalSpace Bb] [ChartedSpace Hb Bb] [IsManifold Ib ∞ Bb]
    {b₀ : Bb}
    {Fa : Type*} [NormedAddCommGroup Fa] [NormedSpace ℝ Fa]
    {Fb' : Type*} [NormedAddCommGroup Fb'] [NormedSpace ℝ Fb']
    {ψ : Bb → Fa →L[ℝ] Fa →L[ℝ] ℝ}
    {L : Bb → Fb' →L[ℝ] Fa}
    (hψ : ContMDiffAt Ib 𝓘(ℝ, Fa →L[ℝ] Fa →L[ℝ] ℝ) ∞ ψ b₀)
    (hL : ContMDiffAt Ib 𝓘(ℝ, Fb' →L[ℝ] Fa) ∞ L b₀) :
    ContMDiffAt Ib 𝓘(ℝ, Fb' →L[ℝ] Fb' →L[ℝ] ℝ) ∞
      (fun b => (ψ b).bilinearComp (L b) (L b)) b₀ := by
  have h1 : ContMDiffAt Ib 𝓘(ℝ, Fb' →L[ℝ] Fa →L[ℝ] ℝ) ∞
      (fun b => (ψ b).comp (L b)) b₀ := hψ.clm_comp hL
  have h_flip_isom : ContDiff ℝ ∞ (ContinuousLinearMap.flip :
      (Fb' →L[ℝ] Fa →L[ℝ] ℝ) → (Fa →L[ℝ] Fb' →L[ℝ] ℝ)) := by
    have : ContDiff ℝ ∞ ((ContinuousLinearMap.flipₗᵢ ℝ Fb' Fa ℝ).toContinuousLinearEquiv :
        (Fb' →L[ℝ] Fa →L[ℝ] ℝ) → (Fa →L[ℝ] Fb' →L[ℝ] ℝ)) :=
      (ContinuousLinearMap.flipₗᵢ ℝ Fb' Fa ℝ).toContinuousLinearEquiv.contDiff
    convert this using 1
  have h2 : ContMDiffAt Ib 𝓘(ℝ, Fa →L[ℝ] Fb' →L[ℝ] ℝ) ∞
      (fun b => ((ψ b).comp (L b)).flip) b₀ :=
    h_flip_isom.contMDiff.contMDiffAt.comp b₀ h1
  have h3 : ContMDiffAt Ib 𝓘(ℝ, Fb' →L[ℝ] Fb' →L[ℝ] ℝ) ∞
      (fun b => (((ψ b).comp (L b)).flip).comp (L b)) b₀ := h2.clm_comp hL
  have h_flip_isom' : ContDiff ℝ ∞ (ContinuousLinearMap.flip :
      (Fb' →L[ℝ] Fb' →L[ℝ] ℝ) → (Fb' →L[ℝ] Fb' →L[ℝ] ℝ)) := by
    have : ContDiff ℝ ∞ ((ContinuousLinearMap.flipₗᵢ ℝ Fb' Fb' ℝ).toContinuousLinearEquiv :
        (Fb' →L[ℝ] Fb' →L[ℝ] ℝ) → (Fb' →L[ℝ] Fb' →L[ℝ] ℝ)) :=
      (ContinuousLinearMap.flipₗᵢ ℝ Fb' Fb' ℝ).toContinuousLinearEquiv.contDiff
    convert this using 1
  have h4 : ContMDiffAt Ib 𝓘(ℝ, Fb' →L[ℝ] Fb' →L[ℝ] ℝ) ∞
      (fun b => ((((ψ b).comp (L b)).flip).comp (L b)).flip) b₀ :=
    h_flip_isom'.contMDiff.contMDiffAt.comp b₀ h3
  refine h4.congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)
  intro b
  rfl

private noncomputable def gInnerCharted
    (g : Measure.SmoothRiemannianMetric I M) (x₀ : M) (b : M) : E →L[ℝ] E →L[ℝ] ℝ :=
  ((trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
      (fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) x₀)
    ⟨b, g.inner b⟩).2

omit [FiniteDimensional ℝ E] hI in
private lemma gInnerCharted_contMDiffAt
    (g : Measure.SmoothRiemannianMetric I M) (x₀ : M) :
    ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞
      (gInnerCharted (I := I) (M := M) g x₀) x₀ := by
  have h_section : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) b (g.inner b)) :=
    g.contMDiff
  have h_x₀ : x₀ ∈ (trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
      (fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) x₀).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' x₀
  exact ((trivializationAt _ _ x₀).contMDiffAt_section_iff h_x₀).mp
    h_section.contMDiffAt

omit [FiniteDimensional ℝ E] in
private lemma gInnerCharted_along_inclusion_contMDiffAt
    (g : Measure.SmoothRiemannianMetric I M) (x₀ : BoundaryManifold I M) :
    ContMDiffAt hI.boundaryI 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞
      (fun b : BoundaryManifold I M =>
        gInnerCharted (I := I) (M := M) g (x₀ : M) (b : M)) x₀ := by
  have h_inclusion_at : ContMDiffAt hI.boundaryI I ∞ (boundaryInclusion I M) x₀ :=
    boundaryInclusion_contMDiff.contMDiffAt
  have h_at : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞
      (gInnerCharted (I := I) (M := M) g (x₀ : M)) (x₀ : M) :=
    gInnerCharted_contMDiffAt g (x₀ : M)
  exact h_at.comp x₀ h_inclusion_at

omit [FiniteDimensional ℝ E] hI in
private lemma gInnerCharted_eval
    (g : Measure.SmoothRiemannianMetric I M) (x₀ b : M)
    (hb : b ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) (v w : E) :
    gInnerCharted (I := I) (M := M) g x₀ b v w =
      g.inner b
        ((trivializationAt E (TangentSpace I) x₀).symm b v)
        ((trivializationAt E (TangentSpace I) x₀).symm b w) := by
  change ((trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
    (fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) x₀)
      ⟨b, g.inner b⟩).2 v w = _
  rw [hom_trivializationAt_apply]
  rw [inCoordinates_apply_eq₂ (𝕜 := ℝ) hb hb (Set.mem_univ _)]
  change (trivializationAt ℝ (Bundle.Trivial M ℝ) x₀).linearMapAt ℝ b _ = _
  change (Bundle.Trivial.trivialization M ℝ).linearMapAt ℝ b _ = _
  rw [Bundle.Trivial.linearMapAt_trivialization (𝕜 := ℝ) (B := M) (F := ℝ) b]
  rfl

omit [FiniteDimensional ℝ E] in
private lemma inducedMetricInner_chart_eval
    (g : Measure.SmoothRiemannianMetric I M) (x₀ : BoundaryManifold I M)
    (b : BoundaryManifold I M)
    (hb_ambient : (b : M) ∈ (trivializationAt E (TangentSpace I) (x₀ : M)).baseSet)
    (hb_bdy : b ∈ (trivializationAt hI.boundaryE
        (TangentSpace hI.boundaryI) x₀).baseSet) (v w : hI.boundaryE) :
    ((trivializationAt (hI.boundaryE →L[ℝ] hI.boundaryE →L[ℝ] ℝ)
        (fun y : BoundaryManifold I M =>
          TangentSpace hI.boundaryI y →L[ℝ]
          TangentSpace hI.boundaryI y →L[ℝ] ℝ) x₀)
      ⟨b, inducedMetricInner g b⟩).2 v w =
    gInnerCharted (I := I) (M := M) g (x₀ : M) (b : M)
      ((trivializationAt E (TangentSpace I) (x₀ : M)).continuousLinearMapAt ℝ (b : M)
        (boundaryInclusionMfderiv b ((trivializationAt hI.boundaryE
          (TangentSpace hI.boundaryI) x₀).symm b v)))
      ((trivializationAt E (TangentSpace I) (x₀ : M)).continuousLinearMapAt ℝ (b : M)
        (boundaryInclusionMfderiv b ((trivializationAt hI.boundaryE
          (TangentSpace hI.boundaryI) x₀).symm b w))) := by
  rw [hom_trivializationAt_apply]
  rw [inCoordinates_apply_eq₂ (𝕜 := ℝ) hb_bdy hb_bdy (Set.mem_univ _)]
  change (trivializationAt ℝ (Bundle.Trivial (BoundaryManifold I M) ℝ) x₀).linearMapAt ℝ b _ = _
  change (Bundle.Trivial.trivialization (BoundaryManifold I M) ℝ).linearMapAt ℝ b _ = _
  rw [Bundle.Trivial.linearMapAt_trivialization (𝕜 := ℝ) (B := BoundaryManifold I M) (F := ℝ) b]
  change inducedMetricInner g b _ _ = _
  rw [inducedMetricInner_apply]
  rw [gInnerCharted_eval g (x₀ : M) (b : M) hb_ambient]
  have hM_v : (trivializationAt E (TangentSpace I) (x₀ : M)).symm (b : M)
        ((trivializationAt E (TangentSpace I) (x₀ : M)).continuousLinearMapAt ℝ (b : M)
          (boundaryInclusionMfderiv b ((trivializationAt hI.boundaryE
            (TangentSpace hI.boundaryI) x₀).symm b v)))
      = boundaryInclusionMfderiv b ((trivializationAt hI.boundaryE
            (TangentSpace hI.boundaryI) x₀).symm b v) := by
    have := (trivializationAt E (TangentSpace I) (x₀ : M)).symmL_continuousLinearMapAt
      (R := ℝ) hb_ambient (boundaryInclusionMfderiv b ((trivializationAt hI.boundaryE
        (TangentSpace hI.boundaryI) x₀).symm b v))
    simpa using this
  have hM_w : (trivializationAt E (TangentSpace I) (x₀ : M)).symm (b : M)
        ((trivializationAt E (TangentSpace I) (x₀ : M)).continuousLinearMapAt ℝ (b : M)
          (boundaryInclusionMfderiv b ((trivializationAt hI.boundaryE
            (TangentSpace hI.boundaryI) x₀).symm b w)))
      = boundaryInclusionMfderiv b ((trivializationAt hI.boundaryE
            (TangentSpace hI.boundaryI) x₀).symm b w) := by
    have := (trivializationAt E (TangentSpace I) (x₀ : M)).symmL_continuousLinearMapAt
      (R := ℝ) hb_ambient (boundaryInclusionMfderiv b ((trivializationAt hI.boundaryE
        (TangentSpace hI.boundaryI) x₀).symm b w))
    simpa using this
  rw [hM_v, hM_w]

omit [FiniteDimensional ℝ E] in
private lemma dincl_chart_conjugated_contMDiffAt
    (x₀ : BoundaryManifold I M) :
    ContMDiffAt hI.boundaryI 𝓘(ℝ, hI.boundaryE →L[ℝ] E) ∞
      (fun b : BoundaryManifold I M =>
        ((trivializationAt E (TangentSpace I) (x₀ : M)).continuousLinearMapAt ℝ (b : M)).comp
          ((boundaryInclusionMfderiv b).comp
            ((trivializationAt hI.boundaryE
                (TangentSpace hI.boundaryI) x₀).symmL ℝ b))) x₀ := by
  have h_inclusion_at : ContMDiffAt hI.boundaryI I ∞ (boundaryInclusion I M) x₀ :=
    boundaryInclusion_contMDiff.contMDiffAt
  have h_mfderiv : ContMDiffAt hI.boundaryI 𝓘(ℝ, hI.boundaryE →L[ℝ] E) ∞
      (inTangentCoordinates hI.boundaryI I id (boundaryInclusion I M)
        (mfderiv hI.boundaryI I (boundaryInclusion I M)) x₀) x₀ := by
    have h_top_add : (∞ : WithTop ℕ∞) + 1 ≤ ∞ := by
      have h_eq : (∞ : WithTop ℕ∞) + 1 = (∞ : WithTop ℕ∞) := by
        change ((⊤ : ℕ∞) : WithTop ℕ∞) + 1 = ((⊤ : ℕ∞) : WithTop ℕ∞)
        rfl
      rw [h_eq]
    exact h_inclusion_at.mfderiv_const h_top_add
  have h_nhds : ∀ᶠ b in 𝓝 x₀,
      inTangentCoordinates hI.boundaryI I id (boundaryInclusion I M)
        (mfderiv hI.boundaryI I (boundaryInclusion I M)) x₀ b
      = ((trivializationAt E (TangentSpace I) (x₀ : M)).continuousLinearMapAt ℝ (b : M)).comp
        ((boundaryInclusionMfderiv b).comp
          ((trivializationAt hI.boundaryE
              (TangentSpace hI.boundaryI) x₀).symmL ℝ b)) := by
    have h_nhds_amb : ∀ᶠ b : BoundaryManifold I M in 𝓝 x₀,
        (b : M) ∈ (chartAt H (x₀ : M)).source := by
      have h_open : IsOpen ((chartAt H (x₀ : M)).source) := (chartAt H (x₀ : M)).open_source
      have h_x₀_in : (x₀ : M) ∈ (chartAt H (x₀ : M)).source := mem_chart_source H _
      have h_continuous : Continuous (Subtype.val :
          {x : M // x ∈ I.boundary M} → M) := continuous_subtype_val
      have h_continuous_b : Continuous (fun b : BoundaryManifold I M => (b : M)) :=
        continuous_subtype_val
      exact (h_continuous_b.continuousAt.preimage_mem_nhds (h_open.mem_nhds h_x₀_in))
    have h_nhds_bdy : ∀ᶠ b : BoundaryManifold I M in 𝓝 x₀,
        b ∈ (chartAt hI.boundaryH x₀).source := by
      exact (chartAt hI.boundaryH x₀).open_source.mem_nhds (mem_chart_source _ _)
    filter_upwards [h_nhds_amb, h_nhds_bdy] with b h_amb h_bdy
    have h_inT := inTangentCoordinates_eq_mfderiv_comp
      (I := hI.boundaryI) (I' := I) (𝕜 := ℝ)
      (f := id) (g := boundaryInclusion I M)
      (ϕ := mfderiv hI.boundaryI I (boundaryInclusion I M)) (x₀ := x₀) (x := b)
      (hx := h_bdy) (hy := h_amb)
    have h_clmAt_eq : (trivializationAt E (TangentSpace I) (x₀ : M)).continuousLinearMapAt ℝ (b : M)
        = mfderiv I 𝓘(ℝ, E) (extChartAt I (x₀ : M)) (b : M) :=
      TangentBundle.continuousLinearMapAt_trivializationAt h_amb
    have h_symmL_eq : (trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) x₀).symmL ℝ b
        = mfderivWithin 𝓘(ℝ, hI.boundaryE) hI.boundaryI (extChartAt hI.boundaryI x₀).symm
            (Set.range hI.boundaryI) (extChartAt hI.boundaryI x₀ b) :=
      TangentBundle.symmL_trivializationAt h_bdy
    rw [h_inT]
    change _ = ((trivializationAt E (TangentSpace I) (x₀ : M)).continuousLinearMapAt ℝ (b : M)).comp
        ((boundaryInclusionMfderiv b).comp ((trivializationAt hI.boundaryE
              (TangentSpace hI.boundaryI) x₀).symmL ℝ b))
    rw [h_clmAt_eq, h_symmL_eq]
    rfl
  exact h_mfderiv.congr_of_eventuallyEq h_nhds

omit [FiniteDimensional ℝ E] in
theorem inducedMetricInner_contMDiff
    (g : Measure.SmoothRiemannianMetric I M) :
    ContMDiff hI.boundaryI
      (hI.boundaryI.prod 𝓘(ℝ, hI.boundaryE →L[ℝ] hI.boundaryE →L[ℝ] ℝ)) ∞
      (fun b : BoundaryManifold I M =>
        TotalSpace.mk' (hI.boundaryE →L[ℝ] hI.boundaryE →L[ℝ] ℝ)
          (E := fun y : BoundaryManifold I M =>
            TangentSpace hI.boundaryI y →L[ℝ] TangentSpace hI.boundaryI y →L[ℝ] ℝ)
          b (inducedMetricInner g b)) := by
  by_cases hN : Nonempty hI.boundaryH
  · haveI := hN
    intro x₀
    rw [(trivializationAt _ _ x₀).contMDiffAt_section_iff
      (FiberBundle.mem_baseSet_trivializationAt' x₀)]
    have h_gInner_at : ContMDiffAt hI.boundaryI 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞
        (fun b : BoundaryManifold I M =>
          gInnerCharted (I := I) (M := M) g (x₀ : M) (b : M)) x₀ :=
      gInnerCharted_along_inclusion_contMDiffAt g x₀
    have h_L_at : ContMDiffAt hI.boundaryI 𝓘(ℝ, hI.boundaryE →L[ℝ] E) ∞
        (fun b : BoundaryManifold I M =>
          ((trivializationAt E (TangentSpace I) (x₀ : M)).continuousLinearMapAt ℝ (b : M)).comp
            ((boundaryInclusionMfderiv b).comp
              ((trivializationAt hI.boundaryE
                  (TangentSpace hI.boundaryI) x₀).symmL ℝ b))) x₀ :=
      dincl_chart_conjugated_contMDiffAt x₀
    have h_bilinearComp : ContMDiffAt hI.boundaryI 𝓘(ℝ, hI.boundaryE →L[ℝ] hI.boundaryE →L[ℝ] ℝ) ∞
        (fun b : BoundaryManifold I M =>
          (gInnerCharted (I := I) (M := M) g (x₀ : M) (b : M)).bilinearComp
            (((trivializationAt E (TangentSpace I) (x₀ : M)).continuousLinearMapAt ℝ (b : M)).comp
              ((boundaryInclusionMfderiv b).comp
                ((trivializationAt hI.boundaryE
                    (TangentSpace hI.boundaryI) x₀).symmL ℝ b)))
            (((trivializationAt E (TangentSpace I) (x₀ : M)).continuousLinearMapAt ℝ (b : M)).comp
              ((boundaryInclusionMfderiv b).comp
                ((trivializationAt hI.boundaryE
                    (TangentSpace hI.boundaryI) x₀).symmL ℝ b)))) x₀ :=
      bilinearComp_smooth_at h_gInner_at h_L_at
    refine h_bilinearComp.congr_of_eventuallyEq ?_
    have h_nhds_amb : ∀ᶠ b : BoundaryManifold I M in 𝓝 x₀,
        (b : M) ∈ (trivializationAt E (TangentSpace I) (x₀ : M)).baseSet := by
      have h_open : IsOpen ((trivializationAt E (TangentSpace I) (x₀ : M)).baseSet) :=
        (trivializationAt E (TangentSpace I) (x₀ : M)).open_baseSet
      have h_x₀_in : (x₀ : M) ∈ (trivializationAt E (TangentSpace I) (x₀ : M)).baseSet :=
        FiberBundle.mem_baseSet_trivializationAt' (x₀ : M)
      have h_continuous : Continuous (fun b : BoundaryManifold I M => (b : M)) :=
        continuous_subtype_val
      exact (h_continuous.continuousAt.preimage_mem_nhds (h_open.mem_nhds h_x₀_in))
    have h_nhds_bdy : ∀ᶠ b : BoundaryManifold I M in 𝓝 x₀,
        b ∈ (trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) x₀).baseSet := by
      have h_open : IsOpen ((trivializationAt hI.boundaryE
        (TangentSpace hI.boundaryI) x₀).baseSet) :=
        (trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) x₀).open_baseSet
      have h_x₀_in : x₀ ∈ (trivializationAt hI.boundaryE
        (TangentSpace hI.boundaryI) x₀).baseSet :=
        FiberBundle.mem_baseSet_trivializationAt' x₀
      exact h_open.mem_nhds h_x₀_in
    filter_upwards [h_nhds_amb, h_nhds_bdy] with b hb_amb hb_bdy
    refine ContinuousLinearMap.ext fun v => ContinuousLinearMap.ext fun w => ?_
    rw [ContinuousLinearMap.bilinearComp_apply]
    rw [inducedMetricInner_chart_eval g x₀ b hb_amb hb_bdy v w]
    rfl
  · haveI : IsEmpty hI.boundaryH := not_nonempty_iff.mp hN
    haveI : IsEmpty (BoundaryManifold I M) :=
      BoundaryManifold.isEmpty_of_isEmpty_boundaryH (I := I)
    intro x; exact (IsEmpty.false x).elim

noncomputable def inducedMetric
    (g : Measure.SmoothRiemannianMetric I M) :
    Measure.SmoothRiemannianMetric hI.boundaryI (BoundaryManifold I M) where
  inner := inducedMetricInner g
  symm := inducedMetricInner_symm g
  pos := inducedMetricInner_pos g
  isVonNBounded := inducedMetricInner_isVonNBounded g
  contMDiff := inducedMetricInner_contMDiff g

omit [FiniteDimensional ℝ E] in
@[simp] lemma inducedMetric_inner
    (g : Measure.SmoothRiemannianMetric I M) (b : BoundaryManifold I M) :
    (inducedMetric g).inner b = inducedMetricInner g b := rfl

omit [FiniteDimensional ℝ E] in
@[simp] lemma inducedMetric_inner_apply
    (g : Measure.SmoothRiemannianMetric I M) (b : BoundaryManifold I M)
    (v w : hI.boundaryE) :
    (inducedMetric g).inner b v w = g.inner (b : M) (boundaryInclusionMfderiv b v) (boundaryInclusionMfderiv b w) :=
  inducedMetricInner_apply g b v w

end WithBoundary
end DivergenceTheorem
end Integral
end DifferentialGeometry
