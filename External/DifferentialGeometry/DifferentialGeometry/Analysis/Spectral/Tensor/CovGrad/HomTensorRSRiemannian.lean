import DifferentialGeometry.Geometry.Connection.TensorNabla.SecondOrderHomBundle
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.SingleSlotOperatorFiberNormBound
import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.Inner.TensorRSContRiemannianBundle
import Mathlib.Topology.VectorBundle.Riemannian
import Mathlib.Topology.VectorBundle.Hom
import Mathlib.Topology.Order.Compact


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold Set IsManifold Tensor0SBundle ContinuousLinearMap Filter
open scoped Manifold Topology ContDiff BigOperators InnerProductSpace

namespace DifferentialGeometry.Integral.Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Tensor.TensorRSRiemannianBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable [CompleteSpace E]

section GenericHomOpNorm

private lemma exists_one_lt_mul_sq_lt {c L : ℝ} (h : c < L) :
    ∃ r : ℝ, 1 < r ∧ c * r ^ 2 < L := by
  have htend : Tendsto (fun r : ℝ => c * r ^ 2) (𝓝 1) (𝓝 c) := by
    have h1 : Tendsto (fun r : ℝ => c * r ^ 2) (𝓝 1) (𝓝 (c * (1 : ℝ) ^ 2)) :=
      tendsto_const_nhds.mul ((continuous_pow 2).tendsto 1)
    simpa using h1
  have hev : ∀ᶠ r in 𝓝 (1 : ℝ), c * r ^ 2 < L := htend.eventually (Iio_mem_nhds h)
  have hev2 : ∀ᶠ r in 𝓝[>] (1 : ℝ), c * r ^ 2 < L := hev.filter_mono nhdsWithin_le_nhds
  rcases (hev2.and self_mem_nhdsWithin).exists with ⟨r, hr2, hr1⟩
  exact ⟨r, hr1, hr2⟩

private lemma continuous_homBundle_opNorm_generic
    {B : Type*} [TopologicalSpace B]
    {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
    {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
    {E₁ : B → Type*} [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, NormedAddCommGroup (E₁ x)]
      [∀ x, InnerProductSpace ℝ (E₁ x)]
      [FiberBundle F₁ E₁] [VectorBundle ℝ F₁ E₁] [IsContinuousRiemannianBundle F₁ E₁]
    {E₂ : B → Type*} [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, NormedAddCommGroup (E₂ x)]
      [∀ x, InnerProductSpace ℝ (E₂ x)]
      [FiberBundle F₂ E₂] [VectorBundle ℝ F₂ E₂] [IsContinuousRiemannianBundle F₂ E₂]
    (Ψ : Π x : B, E₁ x →L[ℝ] E₂ x)
    (hΨ : Continuous (fun x : B => TotalSpace.mk' (F₁ →L[ℝ] F₂)
      (E := fun z : B => E₁ z →L[ℝ] E₂ z) x (Ψ x))) :
    Continuous (fun x : B => ‖Ψ x‖) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  have hx₀a : x₀ ∈ (trivializationAt F₁ E₁ x₀).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' x₀
  have hx₀c : x₀ ∈ (trivializationAt F₂ E₂ x₀).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' x₀
  have hΦcont : ContinuousAt (fun y : B => ContinuousLinearMap.inCoordinates
      F₁ E₁ F₂ E₂ x₀ y x₀ y (Ψ y)) x₀ := by
    have hcont := hΨ.continuousAt (x := x₀)
    rw [continuousAt_hom_bundle] at hcont
    exact hcont.2
  set Ψtil : B → (E₁ x₀ →L[ℝ] E₂ x₀) := fun y =>
    (((trivializationAt F₂ E₂ x₀).symmL ℝ x₀).comp
        ((trivializationAt F₂ E₂ x₀).continuousLinearMapAt ℝ y)).comp
      ((Ψ y).comp (((trivializationAt F₁ E₁ x₀).symmL ℝ y).comp
        ((trivializationAt F₁ E₁ x₀).continuousLinearMapAt ℝ x₀)))
    with hΨtil_def
  have hΨtilcont : ContinuousAt Ψtil x₀ := by
    rw [hΨtil_def]
    refine (ContinuousAt.clm_comp (g := fun _ : B => ((trivializationAt F₂ E₂ x₀).symmL ℝ x₀))
      (f := fun y : B => (((ContinuousLinearMap.inCoordinates F₁ E₁ F₂ E₂ x₀ y x₀ y (Ψ y))).comp
        ((trivializationAt F₁ E₁ x₀).continuousLinearMapAt ℝ x₀))) continuousAt_const
      (ContinuousAt.clm_comp
        (g := fun y : B => ContinuousLinearMap.inCoordinates F₁ E₁ F₂ E₂ x₀ y x₀ y (Ψ y))
        (f := fun _ : B => (trivializationAt F₁ E₁ x₀).continuousLinearMapAt ℝ x₀)
        hΦcont continuousAt_const)).congr ?_
    filter_upwards with y
    rw [ContinuousLinearMap.inCoordinates]
    simp only [ContinuousLinearMap.comp_assoc]
  have hnormtil : ContinuousAt (fun y => ‖Ψtil y‖) x₀ := hΨtilcont.norm
  have hΨtil_x0 : Ψtil x₀ = Ψ x₀ := by
    rw [hΨtil_def]
    ext v
    simp only [ContinuousLinearMap.comp_apply]
    rw [(trivializationAt F₁ E₁ x₀).symmL_continuousLinearMapAt hx₀a,
      (trivializationAt F₂ E₂ x₀).symmL_continuousLinearMapAt hx₀c]
  have hnormtil_lim : Tendsto (fun y => ‖Ψtil y‖) (𝓝 x₀) (𝓝 ‖Ψ x₀‖) := by
    have h0 : Tendsto (fun y => ‖Ψtil y‖) (𝓝 x₀) (𝓝 ‖Ψtil x₀‖) := hnormtil
    rwa [hΨtil_x0] at h0
  have hbasea : ∀ᶠ y in 𝓝 x₀, y ∈ (trivializationAt F₁ E₁ x₀).baseSet :=
    (trivializationAt F₁ E₁ x₀).open_baseSet.mem_nhds hx₀a
  have hbasec : ∀ᶠ y in 𝓝 x₀, y ∈ (trivializationAt F₂ E₂ x₀).baseSet :=
    (trivializationAt F₂ E₂ x₀).open_baseSet.mem_nhds hx₀c
  have hfwd : ∀ {r : ℝ}, 1 < r → ∀ᶠ y in 𝓝 x₀, ‖Ψtil y‖ ≤ r ^ 2 * ‖Ψ y‖ := by
    intro r hr
    have hSc := eventually_norm_symmL_trivializationAt_self_comp_lt F₂ E₂ x₀ hr
    have hSa' := eventually_norm_symmL_trivializationAt_comp_self_lt F₁ E₁ x₀ hr
    filter_upwards [hSc, hSa'] with y hyc hya
    rw [hΨtil_def]
    calc ‖(((trivializationAt F₂ E₂ x₀).symmL ℝ x₀).comp
              ((trivializationAt F₂ E₂ x₀).continuousLinearMapAt ℝ y)).comp
            ((Ψ y).comp (((trivializationAt F₁ E₁ x₀).symmL ℝ y).comp
              ((trivializationAt F₁ E₁ x₀).continuousLinearMapAt ℝ x₀)))‖
        ≤ ‖((trivializationAt F₂ E₂ x₀).symmL ℝ x₀).comp
              ((trivializationAt F₂ E₂ x₀).continuousLinearMapAt ℝ y)‖ *
            ‖(Ψ y).comp (((trivializationAt F₁ E₁ x₀).symmL ℝ y).comp
              ((trivializationAt F₁ E₁ x₀).continuousLinearMapAt ℝ x₀))‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖((trivializationAt F₂ E₂ x₀).symmL ℝ x₀).comp
              ((trivializationAt F₂ E₂ x₀).continuousLinearMapAt ℝ y)‖ *
            (‖Ψ y‖ * ‖((trivializationAt F₁ E₁ x₀).symmL ℝ y).comp
              ((trivializationAt F₁ E₁ x₀).continuousLinearMapAt ℝ x₀)‖) := by
          gcongr
          exact ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ r * (‖Ψ y‖ * r) := by gcongr
      _ = r ^ 2 * ‖Ψ y‖ := by ring
  have hrev : ∀ {r : ℝ}, 1 < r → ∀ᶠ y in 𝓝 x₀, ‖Ψ y‖ ≤ r ^ 2 * ‖Ψtil y‖ := by
    intro r hr
    have hSc' := eventually_norm_symmL_trivializationAt_comp_self_lt F₂ E₂ x₀ hr
    have hSa := eventually_norm_symmL_trivializationAt_self_comp_lt F₁ E₁ x₀ hr
    filter_upwards [hSc', hSa, hbasea, hbasec] with y hyc hya hya_mem hyc_mem
    have hid : Ψ y =
        (((trivializationAt F₂ E₂ x₀).symmL ℝ y).comp
            ((trivializationAt F₂ E₂ x₀).continuousLinearMapAt ℝ x₀)).comp
          ((Ψtil y).comp (((trivializationAt F₁ E₁ x₀).symmL ℝ x₀).comp
            ((trivializationAt F₁ E₁ x₀).continuousLinearMapAt ℝ y))) := by
      rw [hΨtil_def]
      ext v
      simp only [ContinuousLinearMap.comp_apply]
      rw [(trivializationAt F₁ E₁ x₀).continuousLinearMapAt_symmL hx₀a,
        (trivializationAt F₁ E₁ x₀).symmL_continuousLinearMapAt hya_mem,
        (trivializationAt F₂ E₂ x₀).continuousLinearMapAt_symmL hx₀c,
        (trivializationAt F₂ E₂ x₀).symmL_continuousLinearMapAt hyc_mem]
    rw [hid]
    calc ‖(((trivializationAt F₂ E₂ x₀).symmL ℝ y).comp
              ((trivializationAt F₂ E₂ x₀).continuousLinearMapAt ℝ x₀)).comp
            ((Ψtil y).comp (((trivializationAt F₁ E₁ x₀).symmL ℝ x₀).comp
              ((trivializationAt F₁ E₁ x₀).continuousLinearMapAt ℝ y)))‖
        ≤ ‖((trivializationAt F₂ E₂ x₀).symmL ℝ y).comp
              ((trivializationAt F₂ E₂ x₀).continuousLinearMapAt ℝ x₀)‖ *
            ‖(Ψtil y).comp (((trivializationAt F₁ E₁ x₀).symmL ℝ x₀).comp
              ((trivializationAt F₁ E₁ x₀).continuousLinearMapAt ℝ y))‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖((trivializationAt F₂ E₂ x₀).symmL ℝ y).comp
              ((trivializationAt F₂ E₂ x₀).continuousLinearMapAt ℝ x₀)‖ *
            (‖Ψtil y‖ * ‖((trivializationAt F₁ E₁ x₀).symmL ℝ x₀).comp
              ((trivializationAt F₁ E₁ x₀).continuousLinearMapAt ℝ y)‖) := by
          gcongr
          exact ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ r * (‖Ψtil y‖ * r) := by gcongr
      _ = r ^ 2 * ‖Ψtil y‖ := by ring
  change Tendsto (fun y => ‖Ψ y‖) (𝓝 x₀) (𝓝 ‖Ψ x₀‖)
  rw [tendsto_order]
  refine ⟨?_, ?_⟩
  · intro c hc
    obtain ⟨r, hr1, hrlt⟩ := exists_one_lt_mul_sq_lt hc
    have hev1 : ∀ᶠ y in 𝓝 x₀, c * r ^ 2 < ‖Ψtil y‖ :=
      hnormtil_lim.eventually (lt_mem_nhds hrlt)
    filter_upwards [hev1, hfwd hr1] with y hy1 hy2
    have hr2pos : (0 : ℝ) < r ^ 2 := by positivity
    have hchain : c * r ^ 2 < ‖Ψ y‖ * r ^ 2 := by
      calc c * r ^ 2 < ‖Ψtil y‖ := hy1
        _ ≤ r ^ 2 * ‖Ψ y‖ := hy2
        _ = ‖Ψ y‖ * r ^ 2 := by ring
    exact lt_of_mul_lt_mul_right hchain (le_of_lt hr2pos)
  · intro c hc
    obtain ⟨r, hr1, hrlt⟩ := exists_one_lt_mul_sq_lt hc
    have hlim2 : Tendsto (fun y => r ^ 2 * ‖Ψtil y‖) (𝓝 x₀) (𝓝 (r ^ 2 * ‖Ψ x₀‖)) :=
      hnormtil_lim.const_mul _
    have hlt2 : r ^ 2 * ‖Ψ x₀‖ < c := by rw [mul_comm]; exact hrlt
    have hev1 : ∀ᶠ y in 𝓝 x₀, r ^ 2 * ‖Ψtil y‖ < c :=
      hlim2.eventually (Iio_mem_nhds hlt2)
    filter_upwards [hev1, hrev hr1] with y hy1 hy2
    exact lt_of_le_of_lt hy2 hy1

end GenericHomOpNorm

section FibrewiseBound

variable (g : SmoothRiemannianMetric I M) (r a c : ℕ) (x : M)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
omit [CompleteSpace E] in
lemma homTensorRS_riemannianFiberNormSq_clm_apply_le
    (A : TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x)
    (v : TensorRSSpace r a I x) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r a I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r a
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r c I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r c
    riemannianFiberNormSq (I := I) (M := M) g r c x (A v) ≤
      ‖A‖ ^ 2 * riemannianFiberNormSq (I := I) (M := M) g r a x v := by
  letI instA : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r a I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r a
  letI instC : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r c I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r c
  rw [riemannianFiberNormSq_eq_bundle_norm_sq' (I := I) (M := M) g r c x (A v),
    riemannianFiberNormSq_eq_bundle_norm_sq' (I := I) (M := M) g r a x v]
  have hle : ‖A v‖ ≤ ‖A‖ * ‖v‖ := A.le_opNorm v
  calc ‖A v‖ ^ 2 ≤ (‖A‖ * ‖v‖) ^ 2 := by
        exact pow_le_pow_left₀ (norm_nonneg _) hle 2
    _ = ‖A‖ ^ 2 * ‖v‖ ^ 2 := by ring

end FibrewiseBound

section OpNormContinuity

variable (g : SmoothRiemannianMetric I M) (r a c : ℕ)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem continuous_homTensorRS_opNorm
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x)
    (hΨ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)
        (E := fun z : M => TensorRSSpace r a I z →L[ℝ] TensorRSSpace r c I z) x (Ψ x))) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r a I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r a
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r c I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r c
    Continuous (fun x : M => ‖Ψ x‖) := by
  letI instA : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r a I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r a
  letI instC : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r c I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r c
  exact continuous_homBundle_opNorm_generic
    (F₁ := TensorRSModel r a ℝ E) (F₂ := TensorRSModel r c ℝ E)
    (E₁ := fun z : M => TensorRSSpace r a I z) (E₂ := fun z : M => TensorRSSpace r c I z)
    Ψ hΨ.continuous

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in

omit [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem exists_uniform_homTensorRS_opNorm_sq
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x)
    (hΨ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)
        (E := fun z : M => TensorRSSpace r a I z →L[ℝ] TensorRSSpace r c I z) x (Ψ x))) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r a I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r a
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r c I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r c
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : M, ‖Ψ x‖ ^ 2 ≤ C := by
  letI instA : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r a I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r a
  letI instC : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r c I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r c
  have hcont : Continuous (fun x : M => ‖Ψ x‖) :=
    continuous_homTensorRS_opNorm (I := I) (M := M) g r a c Ψ hΨ
  have hcont_sq : Continuous (fun x : M => ‖Ψ x‖ ^ 2) := hcont.pow 2
  obtain ⟨C₀, hC₀⟩ := (isCompact_range hcont_sq).bddAbove
  refine ⟨max C₀ 0, le_max_right _ _, fun x => ?_⟩
  exact le_trans (hC₀ (Set.mem_range_self x)) (le_max_left _ _)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in

omit [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem exists_continuous_homTensorRS_opNorm_sq
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x)
    (hΨ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)
        (E := fun z : M => TensorRSSpace r a I z →L[ℝ] TensorRSSpace r c I z) x (Ψ x))) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r a I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r a
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r c I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r c
    ∃ N : M → ℝ, Continuous N ∧ (∀ x : M, 0 ≤ N x) ∧ ∀ x : M, ‖Ψ x‖ ^ 2 ≤ N x := by
  obtain ⟨C, hC_nonneg, hC_bound⟩ :=
    exists_uniform_homTensorRS_opNorm_sq (I := I) (M := M) g r a c Ψ hΨ
  exact ⟨fun _ => C, continuous_const, fun _ => hC_nonneg, hC_bound⟩

end OpNormContinuity

section Payoff

variable (g : SmoothRiemannianMetric I M) (r a c : ℕ)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in

omit [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem exists_continuous_riemannianFiberNormSq_homTensorRS_section_clm_le
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x)
    (hΨ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)
        (E := fun z : M => TensorRSSpace r a I z →L[ℝ] TensorRSSpace r c I z) x (Ψ x))) :
    ∃ Cop : M → ℝ, Continuous Cop ∧ (∀ x : M, 0 ≤ Cop x) ∧
      ∀ (x : M) (v : TensorRSSpace r a I x),
        riemannianFiberNormSq (I := I) (M := M) g r c x (Ψ x v) ≤
          Cop x * riemannianFiberNormSq (I := I) (M := M) g r a x v := by
  letI instA : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r a I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r a
  letI instC : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r c I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r c
  obtain ⟨N, hN_cont, hN_nonneg, hN_bound⟩ :=
    exists_continuous_homTensorRS_opNorm_sq (I := I) (M := M) g r a c Ψ hΨ
  refine ⟨N, hN_cont, hN_nonneg, fun x v => ?_⟩
  refine le_trans (homTensorRS_riemannianFiberNormSq_clm_apply_le
    (I := I) (M := M) g r a c x (Ψ x) v) ?_
  exact mul_le_mul_of_nonneg_right (hN_bound x)
    (riemannianFiberNormSq_nonneg (I := I) (M := M) g r a x v)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in

omit [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem exists_uniform_riemannianFiberNormSq_homTensorRS_section_clm_le
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x)
    (hΨ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)
        (E := fun z : M => TensorRSSpace r a I z →L[ℝ] TensorRSSpace r c I z) x (Ψ x))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : M) (v : TensorRSSpace r a I x),
      riemannianFiberNormSq (I := I) (M := M) g r c x (Ψ x v) ≤
        C * riemannianFiberNormSq (I := I) (M := M) g r a x v := by
  obtain ⟨Cop, hCop_cont, hCop_nn, hCop_bound⟩ :=
    exists_continuous_riemannianFiberNormSq_homTensorRS_section_clm_le
      (I := I) (M := M) g r a c Ψ hΨ
  have hCpt := (isCompact_univ (X := M)).image hCop_cont
  obtain ⟨C₀, hC₀⟩ := hCpt.bddAbove
  refine ⟨max C₀ 0, le_max_right _ _, fun x v => ?_⟩
  have hCop_le : Cop x ≤ max C₀ 0 :=
    le_trans (hC₀ ⟨x, Set.mem_univ _, rfl⟩) (le_max_left _ _)
  refine le_trans (hCop_bound x v) ?_
  exact mul_le_mul_of_nonneg_right hCop_le
    (riemannianFiberNormSq_nonneg (I := I) (M := M) g r a x v)

end Payoff

end DifferentialGeometry.Integral.Connection
