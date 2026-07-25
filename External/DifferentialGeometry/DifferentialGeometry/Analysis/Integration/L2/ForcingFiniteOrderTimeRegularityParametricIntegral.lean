import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.MaxRegInteriorTimeSmoothing
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.SmoothCoordinateJetPreservation
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.SobolevNonlinearityExistence
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.PointwiseSpectralCoordinate
import DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.Plancherel
import DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.PerModeL2
import DifferentialGeometry.Analysis.Calculus.ContDiffExtendInterval


noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators NNReal
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private theorem fiber_contDiffOn_Icc_finiteOrder
    (f : M → ℝ → ℝ) {T : ℝ} {n : WithTop ℕ∞}
    (hf : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) n (fun p : M × ℝ => f p.1 p.2)
      ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T)) (x : M) :
    ContDiffOn ℝ n (fun u : ℝ => f x u) (Set.Icc (0 : ℝ) T) := by
  have harg : ContMDiffOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)) n (fun u : ℝ => (x, u))
      (Set.Icc (0 : ℝ) T) :=
    (contMDiffOn_const (c := x)).prodMk contMDiffOn_id
  have hmaps : Set.MapsTo (fun u : ℝ => (x, u)) (Set.Icc (0 : ℝ) T)
      ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) := fun u hu => ⟨Set.mem_univ _, hu⟩
  have hcomp := hf.comp harg hmaps
  rw [contMDiffOn_iff_contDiffOn] at hcomp
  exact hcomp

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private theorem partialSnd_contMDiffOn_Icc_finiteOrder
    (f : M → ℝ → ℝ) {T : ℝ} (N : ℕ)
    (hf : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ((N : WithTop ℕ∞) + 1)
      (fun p : M × ℝ => f p.1 p.2) ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (N : WithTop ℕ∞)
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
  rw [hrw]
  intro p₀ hp₀
  have hf' : ContMDiffWithinAt ((I.prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ)
      ((N : WithTop ℕ∞) + 1)
      (Function.uncurry (fun (p : M × ℝ) (s : ℝ) => f p.1 s))
      (((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) ×ˢ Set.Icc (0 : ℝ) T) (p₀, p₀.2) := by
    have harg : ContMDiffWithinAt ((I.prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ))
        ((N : WithTop ℕ∞) + 1)
        (fun q : (M × ℝ) × ℝ => (q.1.1, q.2))
        (((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) ×ˢ Set.Icc (0 : ℝ) T) (p₀, p₀.2) :=
      (contMDiffWithinAt_fst.fst).prodMk contMDiffWithinAt_snd
    have hmaps : Set.MapsTo (fun q : (M × ℝ) × ℝ => (q.1.1, q.2))
        (((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) ×ˢ Set.Icc (0 : ℝ) T)
        ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) :=
      fun q hq => ⟨Set.mem_univ _, hq.2⟩
    exact (hf (p₀.1, p₀.2) ⟨Set.mem_univ _, hp₀.2⟩).comp (p₀, p₀.2) harg hmaps
  have h_apply :=
    ContMDiffWithinAt.mfderivWithin_apply
      (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, ℝ))
      (f := fun (p : M × ℝ) (s : ℝ) => f p.1 s)
      (g := fun p : M × ℝ => p.2) (g₁ := fun p : M × ℝ => p)
      (g₂ := fun _ : M × ℝ => (1 : ℝ))
      (t := (Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T)
      (u := Set.Icc (0 : ℝ) T)
      (v := (Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T)
      (x₀ := p₀) (n := (N : WithTop ℕ∞) + 1) (m := (N : WithTop ℕ∞))
      hf'
      contMDiffWithinAt_snd contMDiffWithinAt_id contMDiffWithinAt_const le_rfl
      (Set.mapsTo_id _) hp₀
      (fun q hq => hq.2) hUM
  simpa [inTangentCoordinates_model_space] using h_apply

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] in
private theorem hasDerivWithinAt_integral_param_Icc_finiteOrder
    (μ : Measure M) [IsFiniteMeasure μ] (f : M → ℝ → ℝ) {T : ℝ} (hT : 0 < T)
    (hf : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (1 : WithTop ℕ∞)
      (fun p : M × ℝ => f p.1 p.2) ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T))
    {t₀ : ℝ} (ht₀ : t₀ ∈ Set.Icc (0 : ℝ) T) :
    HasDerivWithinAt (fun t => ∫ x, f x t ∂μ)
      (∫ x, derivWithin (fun s => f x s) (Set.Icc (0 : ℝ) T) t₀ ∂μ) (Set.Icc (0 : ℝ) T) t₀ := by
  set s : Set ℝ := Set.Icc (0 : ℝ) T with hs_def
  have hconv : Convex ℝ s := convex_Icc 0 T
  have hUD : UniqueDiffOn ℝ s := uniqueDiffOn_Icc hT
  set Fd : M → ℝ → ℝ := fun x t => derivWithin (fun u => f x u) s t with hFd
  have hf_cont : ContinuousOn (fun p : M × ℝ => f p.1 p.2)
      ((Set.univ : Set M) ×ˢ s) := hf.continuousOn
  have hFd_joint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ((0 : ℕ) : WithTop ℕ∞)
      (fun p : M × ℝ => Fd p.1 p.2) ((Set.univ : Set M) ×ˢ s) :=
    partialSnd_contMDiffOn_Icc_finiteOrder f 0
      (by rw [Nat.cast_zero, zero_add]; exact hf)
  have hFd_cont : ContinuousOn (fun p : M × ℝ => Fd p.1 p.2)
      ((Set.univ : Set M) ×ˢ s) := hFd_joint.continuousOn
  have hKcompact : IsCompact ((Set.univ : Set M) ×ˢ s) :=
    isCompact_univ.prod (isCompact_Icc)
  obtain ⟨C, hC⟩ := hKcompact.exists_bound_of_continuousOn hFd_cont
  have hfiber_deriv : ∀ x : M, ∀ y ∈ s, HasDerivWithinAt (fun u => f x u) (Fd x y) s y := by
    intro x y hy
    have hcd : ContDiffOn ℝ (1 : WithTop ℕ∞) (fun u : ℝ => f x u) s :=
      fiber_contDiffOn_Icc_finiteOrder f hf x
    exact ((hcd.differentiableOn one_ne_zero y hy)).hasDerivWithinAt
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
  · have hmeas : ∀ᶠ t in 𝓝[s \ {t₀}] t₀,
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
        (𝓝 (Fd x t₀)) :=
      Filter.Eventually.of_forall (fun x => (hasDerivWithinAt_iff_tendsto_slope.mp (hfiber x)))
    have := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (μ := μ) (bound := fun _ : M => C)
      (F := fun t x => slope (fun u => f x u) t₀ t)
      (f := fun x => Fd x t₀)
      hmeas hbnd (integrable_const C) hlim
    simpa [hG'] using this

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] in
theorem contDiffOn_integral_of_jointContMDiffOn_Icc_finiteOrder
    (μ : Measure M) [IsFiniteMeasure μ] {T : ℝ} (hT : 0 < T) :
    ∀ (N : ℕ) (f : M → ℝ → ℝ),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (N : WithTop ℕ∞) (fun p : M × ℝ => f p.1 p.2)
        ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) →
      ContDiffOn ℝ (N : WithTop ℕ∞) (fun t : ℝ => ∫ x, f x t ∂μ) (Set.Icc (0 : ℝ) T) := by
  have hUD : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) T) := uniqueDiffOn_Icc hT
  intro N
  induction N with
  | zero =>
      intro f hf
      rw [Nat.cast_zero] at hf
      rw [Nat.cast_zero, contDiffOn_zero]
      have hf_cont : ContinuousOn (fun p : M × ℝ => f p.1 p.2)
          ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) := hf.continuousOn
      obtain ⟨C, hC⟩ :=
        (isCompact_univ.prod isCompact_Icc).exists_bound_of_continuousOn hf_cont
      have hf_slice_cont : ∀ t ∈ Set.Icc (0 : ℝ) T, Continuous (fun x : M => f x t) := by
        intro t ht
        have harg : ContinuousOn (fun x : M => (x, t)) (Set.univ : Set M) := by fun_prop
        have hmaps : Set.MapsTo (fun x : M => (x, t)) (Set.univ : Set M)
            ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) := fun x _ => ⟨Set.mem_univ _, ht⟩
        have := (hf_cont.comp harg hmaps)
        rw [continuousOn_univ] at this
        exact this
      have hfib : ∀ x : M, ContinuousOn (fun u : ℝ => f x u) (Set.Icc (0 : ℝ) T) := by
        intro x
        have hcd := fiber_contDiffOn_Icc_finiteOrder (n := (0 : WithTop ℕ∞)) f hf x
        rw [contDiffOn_zero] at hcd
        exact hcd
      intro t₀ ht₀
      have hkey : Filter.Tendsto (fun t : ℝ => ∫ x, f x t ∂μ)
          (nhdsWithin t₀ (Set.Icc (0 : ℝ) T)) (𝓝 (∫ x, f x t₀ ∂μ)) := by
        refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
          (μ := μ) (bound := fun _ : M => C)
          (F := fun (t : ℝ) (x : M) => f x t) (f := fun x : M => f x t₀)
          ?_ ?_ (integrable_const C) ?_
        · refine eventually_nhdsWithin_of_forall (fun t ht => ?_)
          exact (hf_slice_cont t ht).aestronglyMeasurable
        · refine eventually_nhdsWithin_of_forall (fun t ht => ?_)
          exact Filter.Eventually.of_forall (fun x => hC (x, t) ⟨Set.mem_univ _, ht⟩)
        · exact Filter.Eventually.of_forall (fun x => hfib x t₀ ht₀)
      exact hkey
  | succ n ih =>
      intro f hf
      have hf1 : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (1 : WithTop ℕ∞)
          (fun p : M × ℝ => f p.1 p.2) ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) :=
        hf.of_le (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))
      have hfsucc : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ((n : WithTop ℕ∞) + 1)
          (fun p : M × ℝ => f p.1 p.2) ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) := by
        rw [Nat.cast_succ] at hf
        exact hf
      rw [Nat.cast_succ, contDiffOn_succ_iff_derivWithin hUD]
      refine ⟨?_, ?_, ?_⟩
      · exact fun t₀ ht₀ =>
          (hasDerivWithinAt_integral_param_Icc_finiteOrder
            μ f hT hf1 ht₀).differentiableWithinAt
      · intro hcontra; exact absurd hcontra (by simp)
      · have hderiv_eq : Set.EqOn
            (derivWithin (fun t : ℝ => ∫ x, f x t ∂μ) (Set.Icc (0 : ℝ) T))
            (fun t : ℝ => ∫ x, derivWithin (fun s => f x s) (Set.Icc (0 : ℝ) T) t ∂μ)
            (Set.Icc (0 : ℝ) T) := by
          intro t₀ ht₀
          exact (hasDerivWithinAt_integral_param_Icc_finiteOrder
            μ f hT hf1 ht₀).derivWithin (hUD t₀ ht₀)
        refine ContDiffOn.congr ?_ hderiv_eq
        exact ih (fun x t => derivWithin (fun s => f x s) (Set.Icc (0 : ℝ) T) t)
          (partialSnd_contMDiffOn_Icc_finiteOrder f n hfsucc)

theorem clm_comm_iteratedDerivWithin_finiteOrder {V W : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (L : V →L[ℝ] W) (γ : ℝ → V) {T : ℝ} (hT : 0 < T)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) (j : ℕ)
    (hγ : ContDiffWithinAt ℝ (j : WithTop ℕ∞) γ (Set.Icc (0 : ℝ) T) t) :
    iteratedDerivWithin j (fun s => L (γ s)) (Set.Icc (0 : ℝ) T) t =
      L (iteratedDerivWithin j γ (Set.Icc (0 : ℝ) T) t) := by
  have hUD : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) T) := uniqueDiffOn_Icc hT
  have hcomp : (fun s => L (γ s)) = L ∘ γ := rfl
  rw [iteratedDerivWithin_eq_iteratedFDerivWithin, hcomp,
    L.iteratedFDerivWithin_comp_left hγ hUD ht le_rfl,
    ContinuousLinearMap.compContinuousMultilinearMap_coe,
    iteratedDerivWithin_eq_iteratedFDerivWithin]
  rfl

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] in
theorem iteratedDerivWithin_integral_param_Icc_finiteOrder
    (μ : Measure M) [IsFiniteMeasure μ] {T : ℝ} (hT : 0 < T) :
    ∀ (j : ℕ) (f : M → ℝ → ℝ),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (j : WithTop ℕ∞) (fun p : M × ℝ => f p.1 p.2)
        ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) →
      ∀ t₀ ∈ Set.Icc (0 : ℝ) T,
        iteratedDerivWithin j (fun t => ∫ x, f x t ∂μ) (Set.Icc (0 : ℝ) T) t₀ =
          ∫ x, iteratedDerivWithin j (fun s => f x s) (Set.Icc (0 : ℝ) T) t₀ ∂μ := by
  have hUD : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) T) := uniqueDiffOn_Icc hT
  intro j
  induction j with
  | zero =>
      intro f _ t₀ _
      simp only [iteratedDerivWithin_zero]
  | succ n ih =>
      intro f hf t₀ ht₀
      have hf1 : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (1 : WithTop ℕ∞)
          (fun p : M × ℝ => f p.1 p.2) ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) :=
        hf.of_le (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))
      have hfsucc : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ((n : WithTop ℕ∞) + 1)
          (fun p : M × ℝ => f p.1 p.2) ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) := by
        rw [Nat.cast_succ] at hf
        exact hf
      rw [iteratedDerivWithin_succ']
      set Fd : M → ℝ → ℝ := fun x t => derivWithin (fun u => f x u) (Set.Icc (0 : ℝ) T) t
        with hFd
      have hFd_joint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (n : WithTop ℕ∞)
          (fun p : M × ℝ => Fd p.1 p.2) ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) :=
        partialSnd_contMDiffOn_Icc_finiteOrder f n hfsucc
      have hderiv_eqOn : Set.EqOn (derivWithin (fun t => ∫ x, f x t ∂μ) (Set.Icc (0 : ℝ) T))
          (fun t => ∫ x, Fd x t ∂μ) (Set.Icc (0 : ℝ) T) := by
        intro t ht
        exact (hasDerivWithinAt_integral_param_Icc_finiteOrder μ f hT hf1 ht).derivWithin
          (hUD t ht)
      rw [iteratedDerivWithin_congr hderiv_eqOn ht₀, ih Fd hFd_joint t₀ ht₀]
      refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
      exact (iteratedDerivWithin_succ').symm


end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
