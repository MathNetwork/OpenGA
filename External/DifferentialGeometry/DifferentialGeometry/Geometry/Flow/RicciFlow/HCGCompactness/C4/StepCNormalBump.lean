import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepCPartition
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepBInputs

set_option autoImplicit false
set_option linter.style.longLine false











noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Set
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Geometry.Riemannian.Exponential

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [T2Space M] [T2Space (TangentBundle I M)]



noncomputable def normalBump (g : SmoothRiemannianMetric I M) (p : M)
    (f : ContDiffBump (0 : E)) : M → Real :=
  (normalChartAt (I := I) g p).source.indicator
    (fun q => f (normalChartAt (I := I) g p q))

omit [T2Space M] in
omit [NeZero (Module.finrank Real E)] in
@[simp] theorem normalBump_of_mem (g : SmoothRiemannianMetric I M) (p : M)
    (f : ContDiffBump (0 : E)) {q : M}
    (hq : q ∈ (normalChartAt (I := I) g p).source) :
    normalBump g p f q = f (normalChartAt (I := I) g p q) := by
  unfold normalBump
  exact indicator_of_mem hq _

omit [T2Space M] in
omit [NeZero (Module.finrank Real E)] in
@[simp] theorem normalBump_of_notMem (g : SmoothRiemannianMetric I M) (p : M)
    (f : ContDiffBump (0 : E)) {q : M}
    (hq : q ∉ (normalChartAt (I := I) g p).source) :
    normalBump g p f q = 0 := by
  unfold normalBump
  exact indicator_of_notMem hq _


omit [T2Space M] in
omit [NeZero (Module.finrank Real E)] in
theorem normalBump_mem_Icc (g : SmoothRiemannianMetric I M) (p : M)
    (f : ContDiffBump (0 : E)) (q : M) : normalBump g p f q ∈ Set.Icc (0 : Real) 1 := by
  by_cases hq : q ∈ (normalChartAt (I := I) g p).source
  · rw [normalBump_of_mem g p f hq]
    exact ⟨f.nonneg, f.le_one⟩
  · rw [normalBump_of_notMem g p f hq]
    exact ⟨le_rfl, zero_le_one⟩



omit [T2Space M] in
omit [NeZero (Module.finrank Real E)] in
theorem normalBump_one (g : SmoothRiemannianMetric I M) (p : M)
    (f : ContDiffBump (0 : E)) {q : M}
    (hq : q ∈ (normalChartAt (I := I) g p).source)
    (hinner : normalChartAt (I := I) g p q ∈ Metric.closedBall (0 : E) f.rIn) :
    normalBump g p f q = 1 := by
  rw [normalBump_of_mem g p f hq]
  exact f.one_of_mem_closedBall hinner




theorem normalBump_tsupport (g : SmoothRiemannianMetric I M) (p : M)
    (f : ContDiffBump (0 : E))
    (hr : f.rOut < expMapC2Radius (I := I) g p) :
    tsupport (normalBump g p f) ⊆
      (normalChartAt (I := I) g p).symm '' Metric.closedBall (0 : E) f.rOut := by
  let ψ := normalChartAt (I := I) g p
  have hball_tgt : Metric.closedBall (0 : E) f.rOut ⊆ ψ.target := by
    intro v hv
    rw [Metric.mem_closedBall, dist_zero_right] at hv
    exact ball_subset_normalChartAt_target (I := I) g p (hv.trans_lt hr)
  have hcompact : IsCompact (ψ.symm '' Metric.closedBall (0 : E) f.rOut) := by
    refine (isCompact_closedBall (0 : E) f.rOut).image_of_continuousOn ?_
    have hcont : ContinuousOn ψ.symm ψ.target := by
      simpa only [ψ] using
        (normalChartAt_symm_contMDiffOn (I := I) g p).continuousOn
    exact hcont.mono hball_tgt
  apply closure_minimal ?_ hcompact.isClosed
  intro q hq
  rw [Function.mem_support] at hq
  have hqsrc : q ∈ ψ.source := by
    by_contra hnot
    have hnot' : q ∉ (normalChartAt (I := I) g p).source := by
      simpa only [ψ] using hnot
    exact hq (normalBump_of_notMem g p f hnot')
  have hfne : f (ψ q) ≠ 0 := by
    have hqsrc' : q ∈ (normalChartAt (I := I) g p).source := by
      simpa only [ψ] using hqsrc
    rw [normalBump_of_mem g p f hqsrc'] at hq
    simpa only [ψ] using hq
  have hvball : ψ q ∈ Metric.closedBall (0 : E) f.rOut := by
    have hv : ψ q ∈ Function.support f := by
      simpa only [Function.mem_support] using hfne
    rw [f.support_eq] at hv
    exact Metric.ball_subset_closedBall hv
  refine ⟨ψ q, hvball, ?_⟩
  exact ψ.toPartialEquiv.left_inv hqsrc


theorem normalBump_src (g : SmoothRiemannianMetric I M) (p : M)
    (f : ContDiffBump (0 : E))
    (hr : f.rOut < expMapC2Radius (I := I) g p) :
    tsupport (normalBump g p f) ⊆ (normalChartAt (I := I) g p).source := by
  let ψ := normalChartAt (I := I) g p
  intro q hq
  obtain ⟨v, hv, rfl⟩ := normalBump_tsupport g p f hr hq
  apply ψ.map_target
  rw [Metric.mem_closedBall, dist_zero_right] at hv
  exact ball_subset_normalChartAt_target (I := I) g p (hv.trans_lt hr)



theorem normalBump_contMDiff (g : SmoothRiemannianMetric I M) (p : M)
    (f : ContDiffBump (0 : E))
    (hr : f.rOut < expMapC2Radius (I := I) g p) :
    ContMDiff I 𝓘(Real) ∞ (normalBump g p f) := by
  let ψ := normalChartAt (I := I) g p
  refine contMDiff_of_tsupport fun q hq => ?_
  have hqsrc : q ∈ ψ.source := normalBump_src g p f hr hq
  have heq : Set.EqOn (normalBump g p f) (fun y => f (ψ y)) ψ.source := by
    intro y hy
    have hy' : y ∈ (normalChartAt (I := I) g p).source := by
      simpa only [ψ] using hy
    simpa only [ψ] using normalBump_of_mem g p f hy'
  refine ContMDiffAt.congr_of_eventuallyEq ?_
    (heq.eventuallyEq_of_mem (ψ.open_source.mem_nhds hqsrc))
  obtain ⟨v, hv, hqv⟩ := normalBump_tsupport g p f hr hq
  have hvnorm : ‖v‖ < expMapC2Radius (I := I) g p := by
    rw [Metric.mem_closedBall, dist_zero_right] at hv
    exact hv.trans_lt hr
  have hvtgt : v ∈ ψ.target := by
    exact ball_subset_normalChartAt_target (I := I) g p hvnorm
  have hsymm : ψ.symm v =
      expMap (I := I) g p (show TangentSpace I p from v) := by
    simpa only [ψ] using normalChartAt_symm_apply (I := I) g p hvtgt
  have hqexp : q = expMap (I := I) g p (show TangentSpace I p from v) :=
    hqv.symm.trans hsymm
  have hchart := normalChartAt_contMDiffAt_infty (I := I) g p hvnorm
  rw [← hqexp] at hchart
  exact f.contDiffAt.contMDiffAt.comp q hchart







noncomputable def quadNormal (g : SmoothRiemannianMetric I M) (p : M)
    (f : ContDiffBump (0 : Real)) : M → Real :=
  (normalChartAt (I := I) g p).source.indicator fun q =>
    f (g.inner p (normalChartAt (I := I) g p q)
      (normalChartAt (I := I) g p q))

omit [T2Space M] in
omit [NeZero (Module.finrank Real E)] in
@[simp] theorem quadNormal_of_mem (g : SmoothRiemannianMetric I M) (p : M)
    (f : ContDiffBump (0 : Real)) {q : M}
    (hq : q ∈ (normalChartAt (I := I) g p).source) :
    quadNormal g p f q =
      f (g.inner p (normalChartAt (I := I) g p q)
        (normalChartAt (I := I) g p q)) := by
  unfold quadNormal
  exact indicator_of_mem hq _

omit [T2Space M] in
omit [NeZero (Module.finrank Real E)] in
@[simp] theorem quadNormal_of_notMem (g : SmoothRiemannianMetric I M) (p : M)
    (f : ContDiffBump (0 : Real)) {q : M}
    (hq : q ∉ (normalChartAt (I := I) g p).source) :
    quadNormal g p f q = 0 := by
  unfold quadNormal
  exact indicator_of_notMem hq _


omit [T2Space M] in
omit [NeZero (Module.finrank Real E)] in
theorem quadNormal_mem_Icc (g : SmoothRiemannianMetric I M) (p : M)
    (f : ContDiffBump (0 : Real)) (q : M) :
    quadNormal g p f q ∈ Set.Icc (0 : Real) 1 := by
  by_cases hq : q ∈ (normalChartAt (I := I) g p).source
  · rw [quadNormal_of_mem g p f hq]
    exact ⟨f.nonneg, f.le_one⟩
  · rw [quadNormal_of_notMem g p f hq]
    exact ⟨le_rfl, zero_le_one⟩



omit [T2Space M] in
omit [NeZero (Module.finrank Real E)] in
theorem quadNormal_one (g : SmoothRiemannianMetric I M) (p : M)
    (f : ContDiffBump (0 : Real)) {q : M}
    (hq : q ∈ (normalChartAt (I := I) g p).source)
    (hinner : g.inner p (normalChartAt (I := I) g p q)
      (normalChartAt (I := I) g p q) ∈ Metric.closedBall (0 : Real) f.rIn) :
    quadNormal g p f q = 1 := by
  rw [quadNormal_of_mem g p f hq]
  exact f.one_of_mem_closedBall hinner




theorem quadNormal_tsupport (g : SmoothRiemannianMetric I M) (p : M)
    (f : ContDiffBump (0 : Real))
    (hr : Real.sqrt f.rOut < expRadiusGp (I := I) g p) :
    tsupport (quadNormal g p f) ⊆
      (normalChartAt (I := I) g p).symm ''
        {v : E | g.inner p v v ≤ f.rOut} := by
  let ψ := normalChartAt (I := I) g p
  let K : Set E := {v : E | g.inner p v v ≤ f.rOut}
  change tsupport (quadNormal g p f) ⊆ ψ.symm '' K
  have hquad : Continuous (fun v : E => g.inner p v v) :=
    (g.inner p).continuous.clm_apply continuous_id
  have hKclosed : IsClosed K := by
    exact isClosed_le hquad continuous_const
  have hKtgt : K ⊆ ψ.target := by
    intro v hv
    have hsqrt : Real.sqrt (g.inner p v v) < expRadiusGp (I := I) g p :=
      (Real.sqrt_le_sqrt hv).trans_lt hr
    have hvnorm : ‖v‖ < expMapC2Radius (I := I) g p :=
      norm_lt_expMapC2Radius_of_sqrt_inner_lt (I := I) g p hsqrt
    simpa only [ψ] using ball_subset_normalChartAt_target (I := I) g p hvnorm
  have hKbounded : Bornology.IsBounded K := by
    rw [isBounded_iff_forall_norm_le]
    refine ⟨expMapC2Radius (I := I) g p, fun v hv => ?_⟩
    have hsqrt : Real.sqrt (g.inner p v v) < expRadiusGp (I := I) g p :=
      (Real.sqrt_le_sqrt hv).trans_lt hr
    exact (norm_lt_expMapC2Radius_of_sqrt_inner_lt (I := I) g p hsqrt).le
  have hKcompact : IsCompact K :=
    Metric.isCompact_of_isClosed_isBounded hKclosed hKbounded
  have himage : IsCompact (ψ.symm '' K) := by
    refine hKcompact.image_of_continuousOn ?_
    have hcont : ContinuousOn ψ.symm ψ.target := by
      simpa only [ψ] using
        (normalChartAt_symm_contMDiffOn (I := I) g p).continuousOn
    exact hcont.mono hKtgt
  apply closure_minimal ?_ himage.isClosed
  intro q hq
  rw [Function.mem_support] at hq
  have hqsrc : q ∈ ψ.source := by
    by_contra hnot
    have hnot' : q ∉ (normalChartAt (I := I) g p).source := by
      simpa only [ψ] using hnot
    exact hq (quadNormal_of_notMem g p f hnot')
  have hfne : f (g.inner p (ψ q) (ψ q)) ≠ 0 := by
    have hqsrc' : q ∈ (normalChartAt (I := I) g p).source := by
      simpa only [ψ] using hqsrc
    rw [quadNormal_of_mem g p f hqsrc'] at hq
    simpa only [ψ] using hq
  have hvK : ψ q ∈ K := by
    have hv : g.inner p (ψ q) (ψ q) ∈ Function.support f := by
      simpa only [Function.mem_support] using hfne
    rw [f.support_eq] at hv
    have hv' := Metric.ball_subset_closedBall hv
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at hv'
    exact (le_abs_self _).trans hv'
  refine ⟨ψ q, hvK, ?_⟩
  exact ψ.toPartialEquiv.left_inv hqsrc



theorem quadNormal_contMDiff (g : SmoothRiemannianMetric I M) (p : M)
    (f : ContDiffBump (0 : Real))
    (hr : Real.sqrt f.rOut < expRadiusGp (I := I) g p) :
    ContMDiff I (modelWithCornersSelf Real Real) ∞ (quadNormal g p f) := by
  let ψ := normalChartAt (I := I) g p
  refine contMDiff_of_tsupport fun q hq => ?_
  obtain ⟨v, hv, hqv⟩ := quadNormal_tsupport g p f hr hq
  have hsqrt : Real.sqrt (g.inner p v v) < expRadiusGp (I := I) g p :=
    (Real.sqrt_le_sqrt hv).trans_lt hr
  have hvnorm : ‖v‖ < expMapC2Radius (I := I) g p :=
    norm_lt_expMapC2Radius_of_sqrt_inner_lt (I := I) g p hsqrt
  have hvtgt : v ∈ ψ.target := by
    simpa only [ψ] using ball_subset_normalChartAt_target (I := I) g p hvnorm
  have hqsrc : q ∈ ψ.source := by
    rw [← hqv]
    exact ψ.map_target hvtgt
  have heq : Set.EqOn (quadNormal g p f)
      (fun y => f (g.inner p (ψ y) (ψ y))) ψ.source := by
    intro y hy
    have hy' : y ∈ (normalChartAt (I := I) g p).source := by
      simpa only [ψ] using hy
    simpa only [ψ] using quadNormal_of_mem g p f hy'
  refine ContMDiffAt.congr_of_eventuallyEq ?_
    (heq.eventuallyEq_of_mem (ψ.open_source.mem_nhds hqsrc))
  have hsymm : ψ.symm v =
      expMap (I := I) g p (show TangentSpace I p from v) := by
    simpa only [ψ] using normalChartAt_symm_apply (I := I) g p hvtgt
  have hqexp : q = expMap (I := I) g p (show TangentSpace I p from v) :=
    hqv.symm.trans hsymm
  have hchart := normalChartAt_contMDiffAt_infty (I := I) g p hvnorm
  rw [← hqexp] at hchart
  have hscalar : ContDiff Real ∞ (fun w : E => f (g.inner p w w)) :=
    f.contDiff.comp ((g.inner p).contDiff.clm_apply contDiff_id)
  exact hscalar.contDiffAt.contMDiffAt.comp q hchart

section NormalRaw

variable {ι : Type*} [DecidableEq ι]




noncomputable def normalRaw (g : SmoothRiemannianMetric I M) (p : ι → M)
    (cut : ContDiffBump (0 : E)) (f : ι → ContDiffBump (0 : E))
    (i0 i : ι) (q : M) : Real :=
  if i = i0 then normalBump g (p i0) (f i0) q
  else (1 - normalBump g (p i0) cut q) * normalBump g (p i) (f i) q


omit [T2Space M] in
omit [NeZero (Module.finrank Real E)] in
@[simp] theorem normalRaw_same (g : SmoothRiemannianMetric I M) (p : ι → M)
    (cut : ContDiffBump (0 : E)) (f : ι → ContDiffBump (0 : E)) (i0 : ι) :
    normalRaw g p cut f i0 i0 = normalBump g (p i0) (f i0) := by
  funext q
  rw [normalRaw, if_pos rfl]



omit [T2Space M] in
omit [NeZero (Module.finrank Real E)] in
theorem normalRaw_of_ne (g : SmoothRiemannianMetric I M) (p : ι → M)
    (cut : ContDiffBump (0 : E)) (f : ι → ContDiffBump (0 : E)) (i0 i : ι)
    (hi : i ≠ i0) :
    normalRaw g p cut f i0 i = fun q =>
      (1 - normalBump g (p i0) cut q) * normalBump g (p i) (f i) q := by
  funext q
  rw [normalRaw, if_neg hi]



theorem normalRaw_contMDiff (g : SmoothRiemannianMetric I M) (p : ι → M)
    (cut : ContDiffBump (0 : E)) (f : ι → ContDiffBump (0 : E)) (i0 i : ι)
    (hcut : cut.rOut < expMapC2Radius (I := I) g (p i0))
    (hf : ∀ j, (f j).rOut < expMapC2Radius (I := I) g (p j)) :
    ContMDiff I 𝓘(Real) ∞ (normalRaw g p cut f i0 i) := by
  by_cases hi : i = i0
  · subst i
    rw [normalRaw_same]
    exact normalBump_contMDiff g (p i0) (f i0) (hf i0)
  · rw [normalRaw_of_ne g p cut f i0 i hi]
    exact (contMDiff_const.sub (normalBump_contMDiff g (p i0) cut hcut)).mul
      (normalBump_contMDiff g (p i) (f i) (hf i))


omit [T2Space M] in
omit [NeZero (Module.finrank Real E)] in
theorem normalRaw_nonneg (g : SmoothRiemannianMetric I M) (p : ι → M)
    (cut : ContDiffBump (0 : E)) (f : ι → ContDiffBump (0 : E))
    (i0 i : ι) (q : M) : 0 ≤ normalRaw g p cut f i0 i q := by
  by_cases hi : i = i0
  · subst i
    simpa only [normalRaw, if_pos] using (normalBump_mem_Icc g (p i0) (f i0) q).1
  · rw [normalRaw, if_neg hi]
    exact mul_nonneg (sub_nonneg.mpr (normalBump_mem_Icc g (p i0) cut q).2)
      (normalBump_mem_Icc g (p i) (f i) q).1



omit [T2Space M] in
omit [NeZero (Module.finrank Real E)] in
theorem normalRaw_tsupport (g : SmoothRiemannianMetric I M) (p : ι → M)
    (cut : ContDiffBump (0 : E)) (f : ι → ContDiffBump (0 : E))
    (i0 i : ι) :
    tsupport (normalRaw g p cut f i0 i) ⊆ tsupport (normalBump g (p i) (f i)) := by
  by_cases hi : i = i0
  · subst i
    rw [normalRaw_same]
  · rw [normalRaw_of_ne g p cut f i0 i hi]
    exact (tsupport_mul_subset_right :
      tsupport (fun q : M =>
        (1 - normalBump g (p i0) cut q) * normalBump g (p i) (f i) q) ⊆
      tsupport (normalBump g (p i) (f i)))




omit [T2Space M] in
omit [NeZero (Module.finrank Real E)] in
theorem normalRaw_readout (g : SmoothRiemannianMetric I M) (p : ι → M)
    (cut : ContDiffBump (0 : E)) (f : ι → ContDiffBump (0 : E))
    (i0 β i : ι) {z : E}
    (hsrc : ∀ j, (normalChartAt (I := I) g (p β)).symm z ∈
      (normalChartAt (I := I) g (p j)).source) :
    normalRaw g p cut f i0 i ((normalChartAt (I := I) g (p β)).symm z) =
      if i = i0 then
        f i0 (normalChartAt (I := I) g (p i0)
          ((normalChartAt (I := I) g (p β)).symm z))
      else
        (1 - cut (normalChartAt (I := I) g (p i0)
          ((normalChartAt (I := I) g (p β)).symm z))) *
        f i (normalChartAt (I := I) g (p i)
          ((normalChartAt (I := I) g (p β)).symm z)) := by
  by_cases hi : i = i0
  · subst i
    rw [normalRaw, if_pos rfl, if_pos rfl,
      normalBump_of_mem g (p i0) (f i0) (hsrc i0)]
  · rw [normalRaw, if_neg hi, if_neg hi,
      normalBump_of_mem g (p i0) cut (hsrc i0),
      normalBump_of_mem g (p i) (f i) (hsrc i)]

end NormalRaw

end HCGCompactness
end DifferentialGeometry
