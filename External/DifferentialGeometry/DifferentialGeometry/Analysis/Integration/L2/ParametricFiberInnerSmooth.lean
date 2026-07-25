import DifferentialGeometry.Analysis.Integration.L2.Hilbert.Defs
import DifferentialGeometry.Analysis.Integration.L2.Pairing.Defs
import DifferentialGeometry.Analysis.Integration.Measure.Properties
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.ContMDiffMap
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Normed.Group.Bounded


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Manifold MeasureTheory Set Filter Bundle Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators Matrix
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry

theorem contMDiff_partial_deriv_snd
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (F : C^∞⟮I.prod 𝓘(ℝ, ℝ), M × ℝ; ℝ⟯) :
    ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : M × ℝ => deriv (fun s => F (p.1, s)) p.2) := by

  have hrw : (fun p : M × ℝ => deriv (fun s => F (p.1, s)) p.2) =
      fun p : M × ℝ => (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s => F (p.1, s)) p.2) (1 : ℝ) := by
    funext p
    rw [mfderiv_eq_fderiv]
    exact (fderiv_apply_one_eq_deriv (f := fun s => F (p.1, s)) (x := p.2)).symm
  rw [hrw, contMDiff_infty]
  intro n p₀
  have harg : ContMDiff ((I.prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) ∞
      (fun q : (M × ℝ) × ℝ => (q.1.1, q.2)) :=
    ContMDiff.prodMk contMDiff_fst.fst contMDiff_snd
  have hF : ContMDiff ((I.prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun q : (M × ℝ) × ℝ => F (q.1.1, q.2)) := F.contMDiff.comp harg
  have h_apply :=
    ContMDiffAt.mfderiv_apply
      (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, ℝ))
      (f := fun (p : M × ℝ) (t : ℝ) => F (p.1, t))
      (g := fun p : M × ℝ => p.2) (g₁ := fun p : M × ℝ => p)
      (g₂ := fun _ : M × ℝ => (1 : ℝ)) (x₀ := p₀) (m := (n : WithTop ℕ∞))
      ((hF.of_le (by exact_mod_cast le_top : ((n : WithTop ℕ∞) + 1) ≤ ∞)).contMDiffAt)
      contMDiffAt_snd contMDiffAt_id contMDiffAt_const le_rfl
  simpa [inTangentCoordinates_model_space] using h_apply

section ParamIntegral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [T2Space M] [MeasurableSpace M] [OpensMeasurableSpace M]

private theorem hasDerivAt_integral_param
    (μ : Measure M) [IsFiniteMeasure μ] (f : M → ℝ → ℝ)
    (hf : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ (fun p : M × ℝ => f p.1 p.2)) (t₀ : ℝ) :
    HasDerivAt (fun t => ∫ x, f x t ∂μ) (∫ x, deriv (fun s => f x s) t₀ ∂μ) t₀ := by
  set Fd : M → ℝ → ℝ := fun x t => deriv (fun s => f x s) t with hFd
  have hf_cont : Continuous (fun p : M × ℝ => f p.1 p.2) := hf.continuous
  have hFd_joint : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ (fun p : M × ℝ => Fd p.1 p.2) := by
    have := DifferentialGeometry.contMDiff_partial_deriv_snd I
      (⟨fun p : M × ℝ => f p.1 p.2, hf⟩ : C^∞⟮I.prod 𝓘(ℝ, ℝ), M × ℝ; ℝ⟯)
    simpa [hFd] using this
  have hFd_cont : Continuous (fun p : M × ℝ => Fd p.1 p.2) := hFd_joint.continuous
  set s : Set ℝ := Metric.ball t₀ 1 with hs_def
  have hs_nhds : s ∈ 𝓝 t₀ := Metric.ball_mem_nhds t₀ one_pos
  have hKcompact : IsCompact ((Set.univ : Set M) ×ˢ Metric.closedBall t₀ 1) :=
    isCompact_univ.prod (isCompact_closedBall t₀ 1)
  obtain ⟨C, hC⟩ := hKcompact.exists_bound_of_continuousOn hFd_cont.continuousOn
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun t x => f x t) (F' := fun t x => Fd x t) (x₀ := t₀)
    (bound := fun _ : M => C) (μ := μ) (s := s) hs_nhds
    (Filter.Eventually.of_forall (fun t =>
      (hf_cont.comp (by fun_prop : Continuous (fun x : M => (x, t)))).aestronglyMeasurable))
    (integrableOn_univ.mp
      ((hf_cont.comp (by fun_prop : Continuous (fun x : M => (x, t₀)))).continuousOn.integrableOn_compact
        isCompact_univ))
    ((hFd_cont.comp (by fun_prop : Continuous (fun x : M => (x, t₀)))).aestronglyMeasurable)
    (Filter.Eventually.of_forall (fun x => fun t ht => by
      have hmem : (x, t) ∈ ((Set.univ : Set M) ×ˢ Metric.closedBall t₀ 1) :=
        ⟨Set.mem_univ x, Metric.ball_subset_closedBall ht⟩
      simpa using hC (x, t) hmem))
    (integrable_const C)
    (Filter.Eventually.of_forall (fun x => fun t _ => by
      have hcd : ContDiff ℝ ∞ (fun u : ℝ => f x u) := by
        have harg : ContMDiff 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)) ∞ (fun u : ℝ => (x, u)) :=
          (contMDiff_const).prodMk contMDiff_id
        exact contMDiff_iff_contDiff.mp (hf.comp harg)
      exact (hcd.differentiable (by norm_num)).differentiableAt.hasDerivAt))
  exact key.2

theorem contDiff_integral_of_jointContMDiff
    (μ : Measure M) [IsFiniteMeasure μ] (f : M → ℝ → ℝ)
    (hf : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ (fun p : M × ℝ => f p.1 p.2)) :
    ContDiff ℝ ∞ (fun t : ℝ => ∫ x, f x t ∂μ) := by
  rw [contDiff_infty]
  intro N
  induction N generalizing f with
  | zero =>
      rw [Nat.cast_zero, contDiff_zero]
      exact continuous_iff_continuousAt.mpr
        (fun t₀ => (hasDerivAt_integral_param μ f hf t₀).continuousAt)
  | succ n ih =>
      rw [Nat.cast_succ, contDiff_succ_iff_deriv]
      refine ⟨?_, ?_, ?_⟩
      · exact fun t₀ => (hasDerivAt_integral_param μ f hf t₀).differentiableAt
      · intro hcontra; exact absurd hcontra (by simp)
      · have hderiv_eq : deriv (fun t : ℝ => ∫ x, f x t ∂μ) =
            fun t : ℝ => ∫ x, deriv (fun s => f x s) t ∂μ := by
          funext t₀; exact (hasDerivAt_integral_param μ f hf t₀).deriv
        rw [hderiv_eq]
        set Fd : M → ℝ → ℝ := fun x t => deriv (fun s => f x s) t with hFd
        have hFd_joint : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ (fun p : M × ℝ => Fd p.1 p.2) := by
          have := DifferentialGeometry.contMDiff_partial_deriv_snd I
            (⟨fun p : M × ℝ => f p.1 p.2, hf⟩ : C^∞⟮I.prod 𝓘(ℝ, ℝ), M × ℝ; ℝ⟯)
          simpa [hFd] using this
        exact ih Fd hFd_joint

omit [IsManifold I ∞ M] [CompactSpace M] [T2Space M] [MeasurableSpace M] [OpensMeasurableSpace M] in
private theorem fiber_contDiffOn_Icc
    (f : M → ℝ → ℝ) {T : ℝ}
    (hf : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ (fun p : M × ℝ => f p.1 p.2)
      ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T)) (x : M) :
    ContDiffOn ℝ ∞ (fun u : ℝ => f x u) (Set.Icc (0 : ℝ) T) := by
  have harg : ContMDiffOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)) ∞ (fun u : ℝ => (x, u))
      (Set.Icc (0 : ℝ) T) :=
    (contMDiffOn_const (c := x)).prodMk contMDiffOn_id
  have hmaps : Set.MapsTo (fun u : ℝ => (x, u)) (Set.Icc (0 : ℝ) T)
      ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) := fun u hu => ⟨Set.mem_univ _, hu⟩
  have hcomp := hf.comp harg hmaps
  rw [contMDiffOn_iff_contDiffOn] at hcomp
  exact hcomp

omit [CompactSpace M] [T2Space M] [MeasurableSpace M] [OpensMeasurableSpace M] in
theorem partialSnd_contMDiffOn_Icc
    (f : M → ℝ → ℝ) {T : ℝ}
    (hf : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ (fun p : M × ℝ => f p.1 p.2)
      ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : M × ℝ => derivWithin (fun s => f p.1 s) (Set.Icc (0 : ℝ) T) p.2)
      ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) := by
  rcases le_or_gt T 0 with hT0 | hT0
  · have hzero : Set.EqOn
        (fun p : M × ℝ => derivWithin (fun s => f p.1 s) (Set.Icc (0 : ℝ) T) p.2)
        (fun _ : M × ℝ => (0 : ℝ)) ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) := by
      intro p hp
      have hnacc : ¬ AccPt p.2 (Filter.principal (Set.Icc (0 : ℝ) T)) := by
        rw [accPt_principal_iff_nhdsWithin]
        have hempty : Set.Icc (0 : ℝ) T \ {p.2} = ∅ := by
          rw [Set.eq_empty_iff_forall_notMem]
          intro y hy
          exact hy.2 (Set.mem_singleton_iff.mpr
            ((Set.subsingleton_Icc_of_ge hT0) hy.1 hp.2))
        rw [hempty, nhdsWithin_empty]
        exact not_neBot.mpr rfl
      exact derivWithin_zero_of_not_accPt hnacc
    exact (contMDiffOn_const (c := (0 : ℝ))).congr hzero
  have hUM : UniqueMDiffOn 𝓘(ℝ, ℝ) (Set.Icc (0 : ℝ) T) :=
    (uniqueDiffOn_Icc hT0).uniqueMDiffOn
  have hrw : (fun p : M × ℝ => derivWithin (fun s => f p.1 s) (Set.Icc (0 : ℝ) T) p.2) =
      fun p : M × ℝ =>
        (mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s => f p.1 s) (Set.Icc (0 : ℝ) T) p.2) (1 : ℝ) := by
    funext p
    rw [mfderivWithin_eq_fderivWithin]
    exact (fderivWithin_derivWithin (𝕜 := ℝ) (f := fun s => f p.1 s)
      (s := Set.Icc (0 : ℝ) T) (x := p.2)).symm
  rw [hrw, contMDiffOn_infty]
  intro n p₀ hp₀
  have hf' : ContMDiffWithinAt ((I.prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (n + 1 : WithTop ℕ∞)
      (Function.uncurry (fun (p : M × ℝ) (s : ℝ) => f p.1 s))
      (((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) ×ˢ Set.Icc (0 : ℝ) T) (p₀, p₀.2) := by
    have harg : ContMDiffWithinAt ((I.prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) ∞
        (fun q : (M × ℝ) × ℝ => (q.1.1, q.2))
        (((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) ×ˢ Set.Icc (0 : ℝ) T) (p₀, p₀.2) :=
      (contMDiffWithinAt_fst.fst).prodMk contMDiffWithinAt_snd
    have hmaps : Set.MapsTo (fun q : (M × ℝ) × ℝ => (q.1.1, q.2))
        (((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) ×ˢ Set.Icc (0 : ℝ) T)
        ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) :=
      fun q hq => ⟨Set.mem_univ _, hq.2⟩
    have hcomp := (hf (p₀.1, p₀.2) ⟨Set.mem_univ _, hp₀.2⟩).comp (p₀, p₀.2) harg hmaps
    exact hcomp.of_le (by exact_mod_cast le_top : ((n : WithTop ℕ∞) + 1) ≤ ∞)
  have h_apply :=
    ContMDiffWithinAt.mfderivWithin_apply
      (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, ℝ))
      (f := fun (p : M × ℝ) (s : ℝ) => f p.1 s)
      (g := fun p : M × ℝ => p.2) (g₁ := fun p : M × ℝ => p)
      (g₂ := fun _ : M × ℝ => (1 : ℝ))
      (t := (Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T)
      (u := Set.Icc (0 : ℝ) T)
      (v := (Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T)
      (x₀ := p₀) (n := (n : WithTop ℕ∞) + 1) (m := (n : WithTop ℕ∞))
      hf'
      contMDiffWithinAt_snd contMDiffWithinAt_id contMDiffWithinAt_const le_rfl
      (Set.mapsTo_id _) hp₀
      (fun q hq => hq.2) hUM
  simpa [inTangentCoordinates_model_space] using h_apply

private theorem hasDerivWithinAt_integral_param_Icc
    (μ : Measure M) [IsFiniteMeasure μ] (f : M → ℝ → ℝ) {T : ℝ} (hT : 0 < T)
    (hf : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ (fun p : M × ℝ => f p.1 p.2)
      ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T))
    {t₀ : ℝ} (ht₀ : t₀ ∈ Set.Icc (0 : ℝ) T) :
    HasDerivWithinAt (fun t => ∫ x, f x t ∂μ)
      (∫ x, derivWithin (fun s => f x s) (Set.Icc (0 : ℝ) T) t₀ ∂μ) (Set.Icc (0 : ℝ) T) t₀ := by
  set s : Set ℝ := Set.Icc (0 : ℝ) T with hs_def
  have hconv : Convex ℝ s := convex_Icc 0 T
  have hUD : UniqueDiffOn ℝ s := uniqueDiffOn_Icc hT
  set Fd : M → ℝ → ℝ := fun x t => derivWithin (fun u => f x u) s t with hFd
  have hf_cont : ContinuousOn (fun p : M × ℝ => f p.1 p.2)
      ((Set.univ : Set M) ×ˢ s) := hf.continuousOn
  have hFd_joint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ (fun p : M × ℝ => Fd p.1 p.2)
      ((Set.univ : Set M) ×ˢ s) := partialSnd_contMDiffOn_Icc f hf
  have hFd_cont : ContinuousOn (fun p : M × ℝ => Fd p.1 p.2)
      ((Set.univ : Set M) ×ˢ s) := hFd_joint.continuousOn
  have hKcompact : IsCompact ((Set.univ : Set M) ×ˢ s) :=
    isCompact_univ.prod (isCompact_Icc)
  obtain ⟨C, hC⟩ := hKcompact.exists_bound_of_continuousOn hFd_cont
  have hfiber_deriv : ∀ x : M, ∀ y ∈ s, HasDerivWithinAt (fun u => f x u) (Fd x y) s y := by
    intro x y hy
    have hcd : ContDiffOn ℝ ∞ (fun u : ℝ => f x u) s := fiber_contDiffOn_Icc f hf x
    exact ((hcd.differentiableOn (by simp) y hy)).hasDerivWithinAt
  have hfiber : ∀ x : M, HasDerivWithinAt (fun u => f x u) (Fd x t₀) s t₀ :=
    fun x => hfiber_deriv x t₀ ht₀
  have hbound : ∀ x : M, ∀ t ∈ s, ‖f x t - f x t₀‖ ≤ C * ‖t - t₀‖ := by
    intro x t ht
    refine Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun y hy => hfiber_deriv x y hy) (fun y hy => ?_) hconv ht₀ ht
    exact hC (x, y) ⟨Set.mem_univ _, hy⟩
  have hf_slice_cont : ∀ t ∈ s, Continuous (fun x : M => f x t) := by
    intro t ht
    have harg : ContinuousOn (fun x : M => (x, t)) (Set.univ : Set M) := by fun_prop
    have hmaps : Set.MapsTo (fun x : M => (x, t)) (Set.univ : Set M)
        ((Set.univ : Set M) ×ˢ s) := fun x _ => ⟨Set.mem_univ _, ht⟩
    have := (hf_cont.comp harg hmaps)
    rw [continuousOn_univ] at this
    exact this
  have hf_int : ∀ t ∈ s, Integrable (fun x : M => f x t) μ := by
    intro t ht
    exact integrableOn_univ.mp
      ((hf_slice_cont t ht).continuousOn.integrableOn_compact isCompact_univ)
  set G : ℝ → ℝ := fun t => ∫ x, f x t ∂μ with hG
  set G' : ℝ := ∫ x, Fd x t₀ ∂μ with hG'
  rw [hasDerivWithinAt_iff_tendsto_slope]
  have hslope_eq : ∀ t : ℝ, t ∈ s \ {t₀} →
      slope G t₀ t = ∫ x, slope (fun u => f x u) t₀ t ∂μ := by
    intro t ht
    have htne : t ≠ t₀ := fun h => ht.2 (Set.mem_singleton_iff.mpr h)
    rw [slope_def_field, hG]
    simp only []
    rw [show (∫ x, f x t ∂μ) - ∫ x, f x t₀ ∂μ
        = ∫ x, (f x t - f x t₀) ∂μ from
      (integral_sub (hf_int t ht.1) (hf_int t₀ ht₀)).symm]
    rw [div_eq_inv_mul, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    simp only [slope_def_field, div_eq_inv_mul]
  have heq : (fun t => ∫ x, slope (fun u => f x u) t₀ t ∂μ) =ᶠ[𝓝[s \ {t₀}] t₀]
      slope G t₀ := by
    rw [Filter.eventuallyEq_iff_exists_mem]
    exact ⟨s \ {t₀}, self_mem_nhdsWithin, fun t ht => (hslope_eq t ht).symm⟩
  refine Filter.Tendsto.congr' heq ?_
  · have hctbl : (𝓝[s \ {t₀}] t₀).IsCountablyGenerated := by infer_instance
    have hmeas : ∀ᶠ t in 𝓝[s \ {t₀}] t₀,
        AEStronglyMeasurable (fun x : M => slope (fun u => f x u) t₀ t) μ := by
      refine eventually_nhdsWithin_of_forall (fun t ht => ?_)
      have : Continuous (fun x : M => slope (fun u => f x u) t₀ t) := by
        simp only [slope_def_field]
        exact ((hf_slice_cont t ht.1).sub (hf_slice_cont t₀ ht₀)).div_const _
      exact this.aestronglyMeasurable
    have hbnd : ∀ᶠ t in 𝓝[s \ {t₀}] t₀,
        ∀ᵐ x ∂μ, ‖slope (fun u => f x u) t₀ t‖ ≤ C := by
      refine eventually_nhdsWithin_of_forall (fun t ht => ?_)
      refine Filter.Eventually.of_forall (fun x => ?_)
      have htne : t ≠ t₀ := fun h => ht.2 (Set.mem_singleton_iff.mpr h)
      have hpos : 0 < ‖t - t₀‖ := by
        rw [norm_pos_iff]; exact sub_ne_zero.mpr htne
      rw [slope_def_field, norm_div, div_le_iff₀ hpos]
      exact hbound x t ht.1
    have hlim : ∀ᵐ x ∂μ, Filter.Tendsto
        (fun t => slope (fun u => f x u) t₀ t) (𝓝[s \ {t₀}] t₀)
        (𝓝 (Fd x t₀)) := by
      refine Filter.Eventually.of_forall (fun x => ?_)
      exact (hasDerivWithinAt_iff_tendsto_slope.mp (hfiber x))
    have := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (μ := μ) (bound := fun _ : M => C)
      (F := fun t x => slope (fun u => f x u) t₀ t)
      (f := fun x => Fd x t₀)
      hmeas hbnd (integrable_const C) hlim
    simpa [hG'] using this

private theorem contDiffOn_integral_of_jointContMDiffOn_Icc_pos
    (μ : Measure M) [IsFiniteMeasure μ] {T : ℝ} (hT : 0 < T) :
    ∀ (N : ℕ) (f : M → ℝ → ℝ),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ (fun p : M × ℝ => f p.1 p.2)
        ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) →
      ContDiffOn ℝ (N : WithTop ℕ∞) (fun t : ℝ => ∫ x, f x t ∂μ) (Set.Icc (0 : ℝ) T) := by
  have hUD : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) T) := uniqueDiffOn_Icc hT
  intro N
  induction N with
  | zero =>
      intro f hf
      rw [Nat.cast_zero, contDiffOn_zero]
      exact fun t₀ ht₀ =>
        (hasDerivWithinAt_integral_param_Icc μ f hT hf ht₀).continuousWithinAt
  | succ n ih =>
      intro f hf
      rw [Nat.cast_succ, contDiffOn_succ_iff_derivWithin hUD]
      refine ⟨?_, ?_, ?_⟩
      · exact fun t₀ ht₀ =>
          (hasDerivWithinAt_integral_param_Icc μ f hT hf ht₀).differentiableWithinAt
      · intro hcontra; exact absurd hcontra (by simp)
      · have hderiv_eq : Set.EqOn (derivWithin (fun t : ℝ => ∫ x, f x t ∂μ) (Set.Icc (0 : ℝ) T))
            (fun t : ℝ => ∫ x, derivWithin (fun s => f x s) (Set.Icc (0 : ℝ) T) t ∂μ)
            (Set.Icc (0 : ℝ) T) := by
          intro t₀ ht₀
          exact (hasDerivWithinAt_integral_param_Icc μ f hT hf ht₀).derivWithin (hUD t₀ ht₀)
        refine ContDiffOn.congr ?_ hderiv_eq
        exact ih (fun x t => derivWithin (fun s => f x s) (Set.Icc (0 : ℝ) T) t)
          (partialSnd_contMDiffOn_Icc f hf)

theorem contDiffOn_integral_of_jointContMDiffOn_Icc
    (μ : Measure M) [IsFiniteMeasure μ] (f : M → ℝ → ℝ) {T : ℝ}
    (hf : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ (fun p : M × ℝ => f p.1 p.2)
      ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T)) :
    ContDiffOn ℝ ∞ (fun t : ℝ => ∫ x, f x t ∂μ) (Set.Icc (0 : ℝ) T) := by
  rcases lt_trichotomy T 0 with hT0 | hT0 | hT
  · rw [Set.Icc_eq_empty (not_le.mpr hT0)]; exact contDiffOn_empty
  · subst hT0
    rw [Set.Icc_self]
    intro t₀ ht₀
    rw [Set.mem_singleton_iff] at ht₀
    subst ht₀
    exact contDiffWithinAt_singleton (𝕜 := ℝ) (f := fun t : ℝ => ∫ x, f x t ∂μ)
  · refine contDiffOn_infty.mpr (fun N => ?_)
    exact contDiffOn_integral_of_jointContMDiffOn_Icc_pos μ hT N f hf

end ParamIntegral

namespace Integral
namespace L2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩


theorem contDiff_integral_fiberInner_of_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M)
    (b : SmoothCcTensor g₀ 0 2)
    (R : ℝ → SmoothCcTensor g₀ 0 2)
    (h_integrand_joint :
      ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
        (fun p : M × ℝ =>
          tensorInnerPointwise (I := I) (M := M) g₀ 0 2 p.1
            (b.toFun p.1) ((R p.2).toFun p.1))) :
    ContDiff ℝ ∞ (fun t => (inner ℝ b (R t) : ℝ)) := by
  haveI : IsFiniteMeasure
      (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g₀
  have hpt : (fun t => (inner ℝ b (R t) : ℝ)) =
      fun t => ∫ x, tensorInnerPointwise (I := I) (M := M) g₀ 0 2 x
        (b.toFun x) ((R t).toFun x)
        ∂(DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) g₀) := by
    funext t
    rw [SmoothCcTensor.inner_def]
    rfl
  rw [hpt]
  exact DifferentialGeometry.contDiff_integral_of_jointContMDiff
    (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) g₀)
    (fun x t => tensorInnerPointwise (I := I) (M := M) g₀ 0 2 x (b.toFun x) ((R t).toFun x))
    h_integrand_joint

theorem contDiffOn_integral_fiberInner_of_jointContMDiffOn_Icc
    (g₀ : SmoothRiemannianMetric I M) {T : ℝ}
    (b : SmoothCcTensor g₀ 0 2)
    (R : ℝ → SmoothCcTensor g₀ 0 2)
    (h_integrand_joint :
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
        (fun p : M × ℝ =>
          tensorInnerPointwise (I := I) (M := M) g₀ 0 2 p.1
            (b.toFun p.1) ((R p.2).toFun p.1))
        ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T)) :
    ContDiffOn ℝ ∞ (fun t => (inner ℝ b (R t) : ℝ)) (Set.Icc (0 : ℝ) T) := by
  haveI : IsFiniteMeasure
      (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g₀
  have hpt : (fun t => (inner ℝ b (R t) : ℝ)) =
      fun t => ∫ x, tensorInnerPointwise (I := I) (M := M) g₀ 0 2 x
        (b.toFun x) ((R t).toFun x)
        ∂(DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) g₀) := by
    funext t
    rw [SmoothCcTensor.inner_def]
    rfl
  rw [hpt]
  exact DifferentialGeometry.contDiffOn_integral_of_jointContMDiffOn_Icc
    (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) g₀)
    (fun x t => tensorInnerPointwise (I := I) (M := M) g₀ 0 2 x (b.toFun x) ((R t).toFun x))
    h_integrand_joint

end L2
end Integral
end DifferentialGeometry

end
