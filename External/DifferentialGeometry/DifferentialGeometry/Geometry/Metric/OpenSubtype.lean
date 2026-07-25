import DifferentialGeometry.Geometry.Metric.Basic
import DifferentialGeometry.Bundle.ClmSectionSmooth
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]





def SmoothRiemannianMetric.restrictOpenInner
    (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M) (x : U) :
    TangentSpace I x →L[Real] TangentSpace I x →L[Real] Real :=
  g.inner (x : M)

@[simp]
theorem SmoothRiemannianMetric.restrictOpenInner_apply
    (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M)
    (x : U) (v w : TangentSpace I x) :
    g.restrictOpenInner (I := I) U x v w = g.inner (x : M) v w := rfl

theorem SmoothRiemannianMetric.restrictOpenInner_symm
    (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M)
    (x : U) (v w : TangentSpace I x) :
    g.restrictOpenInner (I := I) U x v w =
      g.restrictOpenInner (I := I) U x w v :=
  g.symm (x : M) v w

theorem SmoothRiemannianMetric.restrictOpenInner_pos
    (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M)
    (x : U) (v : TangentSpace I x) (hv : v ≠ 0) :
    0 < g.restrictOpenInner (I := I) U x v v :=
  g.pos (x : M) v hv

theorem SmoothRiemannianMetric.restrictOpenInner_isVonNBounded
    (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M) :
    ∀ x : U, Bornology.IsVonNBounded Real
      {v : TangentSpace I x | g.restrictOpenInner (I := I) U x v v < 1} := by
  intro x
  simpa [SmoothRiemannianMetric.restrictOpenInner] using g.isVonNBounded (x : M)

omit [IsManifold I ∞ M] in


theorem hasMFDerivAt_subtype_val (U : TopologicalSpace.Opens M) (x : U) :
    HasMFDerivAt I I (Subtype.val : U → M) x (ContinuousLinearMap.id Real E) := by
  constructor
  · exact continuous_subtype_val.continuousAt
  · let e : OpenPartialHomeomorph U H :=
      (chartAt H (x : M)).subtypeRestr (s := U) (⟨x⟩ : Nonempty U)
    apply HasFDerivWithinAt.congr_of_eventuallyEq (hasFDerivWithinAt_id _ _)
    · apply Filter.eventuallyEq_of_mem (extChartAt_target_mem_nhdsWithin (I := I) x)
      intro y hy
      have hyTarget : I.symm y ∈ e.target := by
        have hy' :
            (∃ z, I z = y) ∧ I.symm y ∈ e.target := by
          simpa [e, extChartAt, TopologicalSpace.Opens.chartAt_eq] using hy
        exact hy'.2
      have hyRange : y ∈ Set.range I := extChartAt_target_subset_range (I := I) x hy
      have hright := e.right_inv hyTarget
      simp only [writtenInExtChartAt, Function.comp_apply, id_eq]
      change I ((chartAt H (x : M)) ((e.symm (I.symm y) : U) : M)) = y
      change (chartAt H (x : M)) ((e.symm (I.symm y) : U) : M) = I.symm y at hright
      rw [hright]
      exact I.right_inv hyRange
    · simp only [writtenInExtChartAt, Function.comp_apply, id_eq]
      have hleft := (extChartAt I x).left_inv (mem_extChartAt_source x)
      rw [hleft]
      rfl

omit [IsManifold I ∞ M] in
theorem mfderiv_subtype_val
    (U : TopologicalSpace.Opens M) (x : U) :
    mfderiv I I (Subtype.val : U → M) x = ContinuousLinearMap.id Real E :=
  (hasMFDerivAt_subtype_val (I := I) U x).mfderiv

omit [IsManifold I ∞ M] in
theorem mfderiv_subtype_val_apply
    (U : TopologicalSpace.Opens M) (x : U) (v : TangentSpace I x) :
    mfderiv I I (Subtype.val : U → M) x v = v := by
  rw [mfderiv_subtype_val (I := I) U x]
  rfl

variable [FiniteDimensional Real E]

theorem SmoothRiemannianMetric.restrictOpenInner_contMDiff
    (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M)
    [SigmaCompactSpace U] [T2Space U] :
    letI : TopologicalSpace U := inferInstance
    letI : ChartedSpace H U := TopologicalSpace.Opens.instChartedSpace
      (H := H) (M := M) (s := U)
    letI : IsManifold I ∞ U :=
      { U.instHasGroupoid (contDiffGroupoid ∞ I) with }
    ContMDiff I (I.prod 𝓘(Real, E →L[Real] E →L[Real] Real)) ∞
      (fun x : U => TotalSpace.mk' (E →L[Real] E →L[Real] Real) x
        (g.restrictOpenInner (I := I) U x)) := by
  letI : TopologicalSpace U := inferInstance
  letI : ChartedSpace H U := TopologicalSpace.Opens.instChartedSpace
    (H := H) (M := M) (s := U)
  letI : IsManifold I ∞ U :=
    { U.instHasGroupoid (contDiffGroupoid ∞ I) with }
  apply cotangentCov_clmSection_smooth_aux
    (V₂ := fun x : U => TangentSpace I x →L[Real] Real)
    (φ := fun x : U => g.restrictOpenInner (I := I) U x)
  intro Y
  apply cotangentCov_clmSection_smooth_aux
    (V₂ := fun _ : U => Real)
    (φ := fun x : U => g.restrictOpenInner (I := I) U x (Y x))
  intro W
  let incl : U → M := Subtype.val
  have hinclTan : ContMDiff I.tangent I.tangent ∞ (tangentMap I I incl) :=
    (contMDiff_subtype_val (I := I) (U := U)).contMDiff_tangentMap (le_refl _)
  have hY :
      ContMDiff I (I.prod 𝓘(Real, E)) ∞
        (fun x : U => TotalSpace.mk' E (x : M) ((mfderiv I I incl x) (Y x))) := by
    simpa [incl, tangentMap] using hinclTan.comp Y.contMDiff
  have hW :
      ContMDiff I (I.prod 𝓘(Real, E)) ∞
        (fun x : U => TotalSpace.mk' E (x : M) ((mfderiv I I incl x) (W x))) := by
    simpa [incl, tangentMap] using hinclTan.comp W.contMDiff
  have hg :
      ContMDiff I (I.prod 𝓘(Real, E →L[Real] E →L[Real] Real)) ∞
        (fun x : U => TotalSpace.mk' (E →L[Real] E →L[Real] Real)
          (E := fun b : M => TangentSpace I b →L[Real] TangentSpace I b →L[Real] Real)
          (x : M) (g.inner (x : M))) := by
    exact g.contMDiff.comp (contMDiff_subtype_val (I := I) (U := U))
  have h_total :
      ContMDiff I (I.prod 𝓘(Real, Real)) ∞
        (fun x : U => TotalSpace.mk' Real
          (E := Bundle.Trivial M Real)
          (x : M) (g.inner (x : M) ((mfderiv I I incl x) (Y x))
            ((mfderiv I I incl x) (W x)))) :=
    ContMDiff.clm_bundle_apply₂
      (E₁ := fun b : M => TangentSpace I b)
      (E₂ := fun b : M => TangentSpace I b)
      (E₃ := fun _ : M => Real)
      (b := fun x : U => (x : M))
      (ψ := fun x : U => g.inner (x : M))
      (v := fun x : U => (mfderiv I I incl x) (Y x))
      (w := fun x : U => (mfderiv I I incl x) (W x))
      hg hY hW
  have h_scalar :
      ContMDiff I 𝓘(Real, Real) ∞
        (fun x : U => g.inner (x : M) (Y x) (W x)) := by
    have h_scalar' :
        ContMDiff I 𝓘(Real, Real) ∞
          (fun x : U => g.inner (x : M) ((mfderiv I I incl x) (Y x))
            ((mfderiv I I incl x) (W x))) := by
      intro x
      have h_at := h_total x
      rw [contMDiffAt_totalSpace] at h_at
      convert h_at.2 using 1
    simpa [incl, mfderiv_subtype_val_apply] using h_scalar'
  intro x
  rw [contMDiffAt_section]
  refine h_scalar.contMDiffAt.congr_of_eventuallyEq ?_
  filter_upwards with y
  rfl


noncomputable def SmoothRiemannianMetric.restrictOpen
    (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M)
    [SigmaCompactSpace U] [T2Space U] :
    letI : TopologicalSpace U := inferInstance
    letI : ChartedSpace H U := TopologicalSpace.Opens.instChartedSpace
      (H := H) (M := M) (s := U)
    letI : IsManifold I ∞ U :=
      { U.instHasGroupoid (contDiffGroupoid ∞ I) with }
    SmoothRiemannianMetric I U where
  inner x := g.restrictOpenInner (I := I) U x
  symm x v w := g.restrictOpenInner_symm (I := I) U x v w
  pos x v hv := g.restrictOpenInner_pos (I := I) U x v hv
  isVonNBounded := g.restrictOpenInner_isVonNBounded (I := I) U
  contMDiff := g.restrictOpenInner_contMDiff (I := I) U

@[simp]
theorem SmoothRiemannianMetric.restrictOpen_inner
    (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M)
    [SigmaCompactSpace U] [T2Space U]
    (x : U) (v w : TangentSpace I x) :
    letI : TopologicalSpace U := inferInstance
    letI : ChartedSpace H U := TopologicalSpace.Opens.instChartedSpace
      (H := H) (M := M) (s := U)
    letI : IsManifold I ∞ U :=
      { U.instHasGroupoid (contDiffGroupoid ∞ I) with }
    (g.restrictOpen (I := I) U).inner x v w = g.inner (x : M) v w := rfl

omit [IsManifold I ∞ M] [FiniteDimensional Real E] in


@[simp] theorem mfderiv_opens_incl {U V : TopologicalSpace.Opens M} (hVU : V ≤ U) (x : V) :
    mfderiv I I (TopologicalSpace.Opens.inclusion hVU : V → U) x =
      ContinuousLinearMap.id Real E := by
  have hinc : MDifferentiableAt I I (TopologicalSpace.Opens.inclusion hVU : V → U) x :=
    ((contMDiff_inclusion hVU).contMDiffAt).mdifferentiableAt
      (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  have hval : MDifferentiableAt I I (Subtype.val : U → M)
      (TopologicalSpace.Opens.inclusion hVU x) :=
    ((contMDiff_subtype_val (I := I) (U := U)).contMDiffAt).mdifferentiableAt
      (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  have hcomp := mfderiv_comp x hval hinc
  change mfderiv I I (Subtype.val : V → M) x =
    (mfderiv I I (Subtype.val : U → M) (TopologicalSpace.Opens.inclusion hVU x)).comp
      (mfderiv I I (TopologicalSpace.Opens.inclusion hVU : V → U) x) at hcomp
  rw [mfderiv_subtype_val (I := I) V x,
    mfderiv_subtype_val (I := I) U (TopologicalSpace.Opens.inclusion hVU x)] at hcomp
  simpa using hcomp.symm



noncomputable def SmoothRiemannianMetric.restrictOpenOfSubset
    {U V : TopologicalSpace.Opens M} (g : SmoothRiemannianMetric I U) (hVU : V ≤ U)
    [SigmaCompactSpace V] [T2Space V] : SmoothRiemannianMetric I V where
  inner x := g.inner (TopologicalSpace.Opens.inclusion hVU x)
  symm x v w := g.symm (TopologicalSpace.Opens.inclusion hVU x) v w
  pos x v hv := g.pos (TopologicalSpace.Opens.inclusion hVU x) v hv
  isVonNBounded x := by
    simpa using g.isVonNBounded (TopologicalSpace.Opens.inclusion hVU x)
  contMDiff := by
    let incl : V → U := TopologicalSpace.Opens.inclusion hVU
    apply cotangentCov_clmSection_smooth_aux
      (V₂ := fun x : V => TangentSpace I x →L[Real] Real)
      (φ := fun x : V => g.inner (incl x))
    intro Y
    apply cotangentCov_clmSection_smooth_aux
      (V₂ := fun _ : V => Real)
      (φ := fun x : V => g.inner (incl x) (Y x))
    intro W
    have hinclTan : ContMDiff I.tangent I.tangent ∞ (tangentMap I I incl) :=
      (contMDiff_inclusion hVU).contMDiff_tangentMap (le_refl _)
    have hY :
        ContMDiff I (I.prod 𝓘(Real, E)) ∞
          (fun x : V => TotalSpace.mk' E (incl x) ((mfderiv I I incl x) (Y x))) := by
      simpa only [Function.comp_apply, tangentMap] using hinclTan.comp Y.contMDiff
    have hW :
        ContMDiff I (I.prod 𝓘(Real, E)) ∞
          (fun x : V => TotalSpace.mk' E (incl x) ((mfderiv I I incl x) (W x))) := by
      simpa only [Function.comp_apply, tangentMap] using hinclTan.comp W.contMDiff
    have hg :
        ContMDiff I (I.prod 𝓘(Real, E →L[Real] E →L[Real] Real)) ∞
          (fun x : V => TotalSpace.mk' (E →L[Real] E →L[Real] Real)
            (E := fun b : U => TangentSpace I b →L[Real] TangentSpace I b →L[Real] Real)
            (incl x) (g.inner (incl x))) := by
      exact g.contMDiff.comp (contMDiff_inclusion hVU)
    have htotal :
        ContMDiff I (I.prod 𝓘(Real, Real)) ∞
          (fun x : V => TotalSpace.mk' Real
            (E := Bundle.Trivial U Real) (incl x)
            (g.inner (incl x) ((mfderiv I I incl x) (Y x))
              ((mfderiv I I incl x) (W x)))) :=
      ContMDiff.clm_bundle_apply₂
        (E₁ := fun b : U => TangentSpace I b)
        (E₂ := fun b : U => TangentSpace I b)
        (E₃ := fun _ : U => Real)
        (b := incl) (ψ := fun x : V => g.inner (incl x))
        (v := fun x : V => (mfderiv I I incl x) (Y x))
        (w := fun x : V => (mfderiv I I incl x) (W x)) hg hY hW
    have hscalar : ContMDiff I 𝓘(Real, Real) ∞
        (fun x : V => g.inner (incl x) (Y x) (W x)) := by
      have hscalar' : ContMDiff I 𝓘(Real, Real) ∞
          (fun x : V => g.inner (incl x) ((mfderiv I I incl x) (Y x))
            ((mfderiv I I incl x) (W x))) := by
        intro x
        have hat := htotal x
        rw [contMDiffAt_totalSpace] at hat
        convert hat.2 using 1
      simpa [incl] using hscalar'
    intro x
    rw [contMDiffAt_section]
    refine hscalar.contMDiffAt.congr_of_eventuallyEq ?_
    filter_upwards with y
    rfl


@[simp] theorem SmoothRiemannianMetric.restrictSubset_inner
    {U V : TopologicalSpace.Opens M} (g : SmoothRiemannianMetric I U) (hVU : V ≤ U)
    [SigmaCompactSpace V] [T2Space V] (x : V) (v w : TangentSpace I x) :
    (g.restrictOpenOfSubset (I := I) hVU).inner x v w =
      g.inner (TopologicalSpace.Opens.inclusion hVU x) v w := rfl

omit [FiniteDimensional Real E] in
private theorem metric_eq_inner
    {g g' : SmoothRiemannianMetric I M}
    (h : ∀ (x : M) (v w : TangentSpace I x), g.inner x v w = g'.inner x v w) :
    g = g' := by
  obtain ⟨i₁, s₁, p₁, b₁, c₁⟩ := g
  obtain ⟨i₂, s₂, p₂, b₂, c₂⟩ := g'
  have hi : i₁ = i₂ :=
    funext fun x => ContinuousLinearMap.ext fun v => ContinuousLinearMap.ext fun w => h x v w
  subst hi
  rfl



@[simp] theorem SmoothRiemannianMetric.restrictOpen_flat
    (g : SmoothRiemannianMetric I M) {U V : TopologicalSpace.Opens M} (hVU : V ≤ U)
    [SigmaCompactSpace U] [T2Space U] [SigmaCompactSpace V] [T2Space V] :
    (g.restrictOpen (I := I) U).restrictOpenOfSubset (I := I) hVU =
      g.restrictOpen (I := I) V := by
  apply metric_eq_inner
  intro x v w
  rfl

end DifferentialGeometry
