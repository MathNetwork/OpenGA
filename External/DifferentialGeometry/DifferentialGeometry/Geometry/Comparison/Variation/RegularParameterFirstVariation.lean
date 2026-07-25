import DifferentialGeometry.Geometry.Connection.ParallelTransport.ParallelTransport
import DifferentialGeometry.Geometry.Comparison.Variation.FixedChartIdentities
import DifferentialGeometry.Geometry.Connection.ParallelTransport.AlongCurve
import DifferentialGeometry.Geometry.Connection.ParallelTransport.CovariantDerivativeAlong
import DifferentialGeometry.Geometry.Connection.ParallelTransport.MFDerivAlongCurve
import DifferentialGeometry.Geometry.Geodesic.Equation
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Defs
import DifferentialGeometry.Geometry.Connection.LeviCivita.Defs
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciIdentity
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciConnection
import DifferentialGeometry.Geometry.Metric.TensorInner.TangentRiemannian
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Topology.VectorBundle.Riemannian
import Mathlib.Topology.Compactness.Compact
import DifferentialGeometry.Geometry.Comparison.Variation.ArcLength
import DifferentialGeometry.Geometry.Comparison.Variation.SpeedDerivative
import DifferentialGeometry.Geometry.Comparison.Variation.FirstVariation
import DifferentialGeometry.Geometry.Comparison.Variation.CovariantCommutationCurvature


noncomputable section

open Set Function Filter Manifold Bundle MeasureTheory intervalIntegral
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Variation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.Geodesic

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem speed_positivity_near
    (g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M) (L s₀ : ℝ)
    (hf : IsSmoothVariation (I := I) f)
    (hpos : ∀ t ∈ Set.Icc (0 : ℝ) L, 0 < speedSq (I := I) g f s₀ t) :
    ∃ δ > (0 : ℝ), ∃ c > (0 : ℝ),
      ∀ s ∈ Set.Ioo (s₀ - δ) (s₀ + δ), ∀ t ∈ Set.Icc 0 L,
        c ≤ Real.sqrt (speedSq (I := I) g f s t) := by
  classical
  have hsq_cont : Continuous (fun p : ℝ × ℝ => speedSq (I := I) g f p.1 p.2) :=
    speedSq_continuous (I := I) (M := M) g f hf
  have hslice_cont : ContinuousOn (fun t : ℝ => speedSq (I := I) g f s₀ t) (Set.Icc 0 L) :=
    (hsq_cont.comp (continuous_const.prodMk continuous_id)).continuousOn
  obtain ⟨m, hm⟩ : ∃ m : ℝ, 0 < m ∧ ∀ t ∈ Set.Icc (0 : ℝ) L, m ≤ speedSq (I := I) g f s₀ t := by
    rcases (Set.eq_empty_or_nonempty (Set.Icc (0 : ℝ) L)) with hEmpty | hNe
    · refine ⟨1, one_pos, fun t ht => ?_⟩
      rw [hEmpty] at ht
      exact ((Set.mem_empty_iff_false t).mp ht).elim
    · obtain ⟨tm, htm_mem, htm_min⟩ :=
        isCompact_Icc.exists_isMinOn hNe hslice_cont
      exact ⟨speedSq (I := I) g f s₀ tm, hpos tm htm_mem, fun t ht => htm_min ht⟩
  obtain ⟨m_pos, hm_lb⟩ := hm
  have hS_open : IsOpen
      ((fun p : ℝ × ℝ => speedSq (I := I) g f p.1 p.2) ⁻¹' Set.Ioi (m / 2 : ℝ)) :=
    isOpen_Ioi.preimage hsq_cont
  have hZ_in_S :
      ({s₀} : Set ℝ) ×ˢ Set.Icc (0 : ℝ) L ⊆
        (fun p : ℝ × ℝ => speedSq (I := I) g f p.1 p.2) ⁻¹' Set.Ioi (m / 2 : ℝ) := by
    intro p hp
    rcases hp with ⟨hp1, hp2⟩
    have hp1' : p.1 = s₀ := hp1
    change (m / 2 : ℝ) < speedSq (I := I) g f p.1 p.2
    rw [hp1']
    have := hm_lb p.2 hp2
    linarith
  obtain ⟨U, V, hU_open, _hV_open, hs₀_in_U, hL_in_V, hUV_in_S⟩ :=
    generalized_tube_lemma isCompact_singleton (isCompact_Icc (a := (0 : ℝ)) (b := L))
      hS_open hZ_in_S
  have hs₀_in_U' : s₀ ∈ U := hs₀_in_U rfl
  rcases Metric.isOpen_iff.mp hU_open s₀ hs₀_in_U' with ⟨δ, δ_pos, hball_U⟩
  refine ⟨δ, δ_pos, Real.sqrt (m / 2), Real.sqrt_pos.mpr (by linarith), ?_⟩
  intro s hs t ht
  have hs_in_U : s ∈ U := by
    apply hball_U
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    rcases hs with ⟨h1, h2⟩
    constructor <;> linarith
  have ht_in_V : t ∈ V := hL_in_V ht
  have h_st_in_S : speedSq (I := I) g f s t > (m / 2 : ℝ) :=
    hUV_in_S (Set.mk_mem_prod hs_in_U ht_in_V)
  exact Real.sqrt_le_sqrt (le_of_lt h_st_in_S)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private theorem S2_diff_under_interval_integral_general
    (g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M) (L s₀ : ℝ)
    (hf : IsSmoothVariation (I := I) f) (hL : 0 < L)
    (hpos : ∀ t ∈ Set.Icc (0 : ℝ) L, 0 < speedSq (I := I) g f s₀ t) :
    HasDerivAt
      (fun s : ℝ => ∫ t in (0 : ℝ)..L, Real.sqrt (speedSq (I := I) g f s t))
      (∫ t in (0 : ℝ)..L,
        fderiv ℝ (fun p : ℝ × ℝ => speedSq (I := I) g f p.1 p.2) (s₀, t) (1, 0)
          / (2 * Real.sqrt (speedSq (I := I) g f s₀ t)))
      s₀ := by
  classical
  set Φ : ℝ → ℝ → ℝ := fun s t => speedSq (I := I) g f s t with hΦdef
  set G : ℝ × ℝ → ℝ := fun p : ℝ × ℝ => Φ p.1 p.2 with hG
  have hΦ : ContDiff ℝ (7 : ℕ) G := by
    rw [hG, hΦdef]; exact speedSq_contDiff (I := I) (M := M) g f hf
  have hΦcont : Continuous G := hΦ.continuous
  have hΦdiff : ∀ p : ℝ × ℝ, DifferentiableAt ℝ G p :=
    fun p => (hΦ.differentiable (by simp)).differentiableAt
  have hslice_deriv : ∀ s t : ℝ,
      HasDerivAt (fun u : ℝ => Φ u t) (fderiv ℝ G (s, t) (1, 0)) s := by
    intro s t
    have := Aux2.hasDerivAt_slice_fst (fun u v => Φ u v) s t (hΦdiff (s, t))
    simpa only [hG] using this
  set Dnum : ℝ → ℝ := fun t : ℝ => fderiv ℝ G (s₀, t) (1, 0) with hDnum
  have hpartial_cont : Continuous (fun p : ℝ × ℝ => fderiv ℝ G p (1, 0)) := by
    have hc : Continuous (fun p : ℝ × ℝ => fderiv ℝ G p) :=
      hΦ.continuous_fderiv (by simp)
    exact hc.clm_apply continuous_const
  have hDcont : Continuous Dnum := by
    have : Continuous (fun t : ℝ => fderiv ℝ G (s₀, t) (1, 0)) :=
      hpartial_cont.comp (continuous_const.prodMk continuous_id)
    exact this
  obtain ⟨δ, hδ, c0, hc0, hposΦ⟩ :=
    speed_positivity_near (I := I) (M := M) g f L s₀ hf hpos
  set δ' : ℝ := δ / 2 with hδ'
  have hδ'pos : 0 < δ' := by positivity
  have hδ'lt : δ' < δ := by simp only [hδ']; linarith
  set Kset : Set (ℝ × ℝ) := Set.Icc (s₀ - δ') (s₀ + δ') ×ˢ Set.Icc 0 L with hKset
  have hKcompact : IsCompact Kset := (isCompact_Icc).prod isCompact_Icc
  have hKne : Kset.Nonempty :=
    ⟨(s₀, 0), ⟨⟨by linarith, by linarith⟩, ⟨le_refl 0, le_of_lt hL⟩⟩⟩
  obtain ⟨pm, hpmKset, hpmMax⟩ := hKcompact.exists_isMaxOn hKne
    ((continuous_norm.comp hpartial_cont).continuousOn)
  set K1 : ℝ := ‖fderiv ℝ G pm (1, 0)‖ with hK1
  have hK1nonneg : 0 ≤ K1 := norm_nonneg _
  have hsqrtlb : ∀ s ∈ Set.Icc (s₀ - δ') (s₀ + δ'), ∀ t ∈ Set.Icc (0 : ℝ) L,
      c0 ≤ Real.sqrt (Φ s t) := by
    intro s hs t ht
    refine hposΦ s ?_ t ht
    rcases hs with ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩
  have hΦne : ∀ s ∈ Set.Icc (s₀ - δ') (s₀ + δ'), ∀ t ∈ Set.Icc (0 : ℝ) L, Φ s t ≠ 0 := by
    intro s hs t ht hcontra
    have hsqrt0 : Real.sqrt (Φ s t) = 0 := by rw [hcontra, Real.sqrt_zero]
    have := hsqrtlb s hs t ht
    rw [hsqrt0] at this; linarith
  set C0 : ℝ := K1 / (2 * c0) with hC0
  have hC0nonneg : 0 ≤ C0 := by positivity
  have hlip : ∀ t ∈ Set.Icc (0 : ℝ) L,
      LipschitzOnWith C0.toNNReal (fun s => Real.sqrt (Φ s t))
        (Set.Icc (s₀ - δ') (s₀ + δ')) := by
    intro t ht
    apply Convex.lipschitzOnWith_of_nnnorm_deriv_le (𝕜 := ℝ) _ _ (convex_Icc _ _)
    · intro s hs
      exact ((hslice_deriv s t).sqrt (hΦne s hs t ht)).differentiableAt
    · intro s hs
      have hderiv_eq : deriv (fun u : ℝ => Real.sqrt (Φ u t)) s
          = fderiv ℝ G (s, t) (1, 0) / (2 * Real.sqrt (Φ s t)) :=
        ((hslice_deriv s t).sqrt (hΦne s hs t ht)).deriv
      have hnum_le : ‖fderiv ℝ G (s, t) (1, 0)‖ ≤ K1 :=
        hpmMax (⟨hs, ht⟩ : (s, t) ∈ Kset)
      have hden_ge : 2 * c0 ≤ 2 * Real.sqrt (Φ s t) := by
        have := hsqrtlb s hs t ht; linarith
      have hden_pos : (0 : ℝ) < 2 * Real.sqrt (Φ s t) := by
        have := hsqrtlb s hs t ht; linarith
      have hnorm_le : ‖deriv (fun u : ℝ => Real.sqrt (Φ u t)) s‖ ≤ C0 := by
        rw [hderiv_eq, norm_div, Real.norm_eq_abs (2 * Real.sqrt (Φ s t)),
          abs_of_nonneg (le_of_lt hden_pos), hC0,
          div_le_div_iff₀ hden_pos (by linarith : (0 : ℝ) < 2 * c0)]
        calc ‖fderiv ℝ G (s, t) (1, 0)‖ * (2 * c0)
              ≤ K1 * (2 * c0) :=
                mul_le_mul_of_nonneg_right hnum_le (by positivity)
          _ ≤ K1 * (2 * Real.sqrt (Φ s t)) :=
                mul_le_mul_of_nonneg_left hden_ge hK1nonneg
      have h1 : ‖deriv (fun u : ℝ => Real.sqrt (Φ u t)) s‖₊
          = Real.toNNReal ‖deriv (fun u : ℝ => Real.sqrt (Φ u t)) s‖ := by
        rw [Real.toNNReal_of_nonneg (norm_nonneg _)]; rfl
      rw [h1]; exact Real.toNNReal_le_toNNReal hnorm_le
  set Ffun : ℝ → ℝ → ℝ := fun s t => Real.sqrt (Φ s t) with hFfun
  set Ffun' : ℝ → ℝ := fun t => Dnum t / (2 * Real.sqrt (Φ s₀ t)) with hFfun'
  have hFcont : ∀ s : ℝ, Continuous (Ffun s) := fun s =>
    Real.continuous_sqrt.comp (hΦcont.comp (continuous_const.prodMk continuous_id))
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_lip
    (μ := volume) (a := (0 : ℝ)) (b := L) (F := Ffun) (F' := Ffun') (x₀ := s₀)
    (bound := fun _ => C0) (s := Set.Ioo (s₀ - δ') (s₀ + δ'))
    (Ioo_mem_nhds (by linarith) (by linarith))
    (Filter.Eventually.of_forall (fun x => (hFcont x).aestronglyMeasurable))
    ((hFcont s₀).intervalIntegrable 0 L)
    (by
      have hden_cont : Continuous (fun t : ℝ => 2 * Real.sqrt (Φ s₀ t)) :=
        continuous_const.mul (Real.continuous_sqrt.comp
          (hΦcont.comp (continuous_const.prodMk continuous_id)))
      have hcoon : ContinuousOn Ffun' (Set.Ioc (0 : ℝ) L) := by
        apply ContinuousOn.div hDcont.continuousOn hden_cont.continuousOn
        intro t ht
        have htIcc : t ∈ Set.Icc (0 : ℝ) L := ⟨le_of_lt ht.1, ht.2⟩
        have h0 : s₀ ∈ Set.Icc (s₀ - δ') (s₀ + δ') := ⟨by linarith, by linarith⟩
        have hsqrt_pos : (0 : ℝ) < Real.sqrt (Φ s₀ t) := by
          have := hsqrtlb s₀ h0 t htIcc; linarith
        exact ne_of_gt (by linarith)
      rw [Set.uIoc_of_le (le_of_lt hL)]
      exact hcoon.aestronglyMeasurable measurableSet_Ioc)
    (by
      apply Filter.Eventually.of_forall
      intro t ht
      rw [Set.uIoc_of_le (le_of_lt hL)] at ht
      have htIcc : t ∈ Set.Icc (0 : ℝ) L := ⟨le_of_lt ht.1, ht.2⟩
      have hnn : Real.nnabs C0 = C0.toNNReal := by
        ext; simp [Real.coe_nnabs, Real.coe_toNNReal _ hC0nonneg,
          abs_of_nonneg hC0nonneg]
      rw [hnn]
      exact (hlip t htIcc).mono Set.Ioo_subset_Icc_self)
    (_root_.intervalIntegrable_const)
    (by
      apply Filter.Eventually.of_forall
      intro t ht
      rw [Set.uIoc_of_le (le_of_lt hL)] at ht
      have htIcc : t ∈ Set.Icc (0 : ℝ) L := ⟨le_of_lt ht.1, ht.2⟩
      have h0 : s₀ ∈ Set.Icc (s₀ - δ') (s₀ + δ') := ⟨by linarith, by linarith⟩
      exact (hslice_deriv s₀ t).sqrt (hΦne s₀ h0 t htIcc))
  exact key.2

omit [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem first_variation_of_arcLength_at_regular_parameter
    (g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M) (L s₀ : ℝ)
    (hf : IsSmoothVariation (I := I) f) (hL : 0 < L)
    (hpos : ∀ t ∈ Set.Icc (0 : ℝ) L, 0 < speedSq (I := I) g f s₀ t) :
    HasDerivAt (fun s' : ℝ => arcLength (I := I) g (fun t : ℝ => f s' t) 0 L)
      (∫ t in (0 : ℝ)..L,
        g.inner (f s₀ t)
          (DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong.covDerivAlong
            (I := I) g (fun s : ℝ => f s t)
            (fun s : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f s u) t (1 : ℝ)) s₀)
          (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f s₀ u) t (1 : ℝ))
          / Real.sqrt (speedSq (I := I) g f s₀ t))
      s₀ := by
  classical
  open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong in
  have harc : (fun s' : ℝ => arcLength (I := I) g (fun t : ℝ => f s' t) 0 L)
      = (fun s' : ℝ => ∫ t in (0 : ℝ)..L, Real.sqrt (speedSq (I := I) g f s' t)) := by
    funext s'; exact arcLength_slice_eq_integral_sqrt_speedSq (I := I) g f s' L
  rw [harc]
  have hS2 := S2_diff_under_interval_integral_general (I := I) g f L s₀ hf hL hpos
  set fsh : ℝ → ℝ → M := fun a b : ℝ => f (s₀ + a) b with hfsh
  have hfsh_smooth : IsSmoothVariation (I := I) fsh := by
    have hshift : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (8 : ℕ)
        (fun q : ℝ × ℝ => (s₀ + q.1, q.2)) :=
      (contMDiff_const.add contMDiff_fst).prodMk contMDiff_snd
    exact (hf : ContMDiff _ _ _ _).comp hshift
  have hG_diff : ∀ p : ℝ × ℝ, DifferentiableAt ℝ
      (fun q : ℝ × ℝ => speedSq (I := I) g f q.1 q.2) p :=
    fun p => ((speedSq_contDiff (I := I) (M := M) g f hf).differentiable
      (by simp)).differentiableAt
  have hintegrand_eq : Set.EqOn
      (fun t : ℝ =>
        fderiv ℝ (fun p : ℝ × ℝ => speedSq (I := I) g f p.1 p.2) (s₀, t) (1, 0)
          / (2 * Real.sqrt (speedSq (I := I) g f s₀ t)))
      (fun t : ℝ =>
        g.inner (f s₀ t)
          (covDerivAlong (I := I) g (fun s : ℝ => f s t)
            (fun s : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f s u) t (1 : ℝ)) s₀)
          (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f s₀ u) t (1 : ℝ))
          / Real.sqrt (speedSq (I := I) g f s₀ t))
      (Set.uIcc 0 L) := by
    intro t _ht
    simp only []
    have hslice_f : HasDerivAt
        (fun a : ℝ => speedSq (I := I) g f (s₀ + a) t)
        (fderiv ℝ (fun p : ℝ × ℝ => speedSq (I := I) g f p.1 p.2) (s₀, t) (1, 0)) 0 := by
      have hslice0 : HasDerivAt (fun u : ℝ => speedSq (I := I) g f u t)
          (fderiv ℝ (fun p : ℝ × ℝ => speedSq (I := I) g f p.1 p.2) (s₀, t) (1, 0)) (s₀ + 0) := by
        rw [add_zero]
        exact Aux2.hasDerivAt_slice_fst
          (fun u v : ℝ => speedSq (I := I) g f u v) s₀ t (hG_diff (s₀, t))
      have hshift : HasDerivAt (fun a : ℝ => s₀ + a) (1 : ℝ) 0 := by
        simpa using (hasDerivAt_id (0 : ℝ)).const_add s₀
      have hcomp := hslice0.comp 0 hshift
      simpa using hcomp
    have hS1 := speedSq_hasDerivAt (I := I) g fsh t hfsh_smooth
    have hspeed_shift : ∀ a : ℝ, speedSq (I := I) g fsh a t
        = speedSq (I := I) g f (s₀ + a) t := fun a => rfl
    have hS1' : HasDerivAt (fun a : ℝ => speedSq (I := I) g f (s₀ + a) t)
        (2 * g.inner (fsh 0 t)
          (covDerivAlong (I := I) g (fun a : ℝ => fsh a t)
            (fun a : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => fsh a u) t (1 : ℝ)) 0)
          (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => fsh 0 u) t (1 : ℝ))) 0 := by
      have heq : (fun a : ℝ => speedSq (I := I) g fsh a t)
          = (fun a : ℝ => speedSq (I := I) g f (s₀ + a) t) := by
        funext a; exact hspeed_shift a
      rw [heq] at hS1; exact hS1
    have hval := hS1'.unique hslice_f
    have hfoot0 : fsh 0 t = f s₀ t := by rw [hfsh]; simp
    have hcov_shift :
        covDerivAlong (I := I) g (fun a : ℝ => fsh a t)
            (fun a : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => fsh a u) t (1 : ℝ)) 0
          = covDerivAlong (I := I) g (fun s : ℝ => f s t)
            (fun s : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f s u) t (1 : ℝ)) s₀ := by
      have := covDerivAlong_const_add_shift (I := I) g (fun s : ℝ => f s t)
        (fun s : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f s u) t (1 : ℝ)) s₀
      exact this
    rw [← hval]
    rw [hfoot0, hcov_shift]
    have hsh_velT : ∀ u : ℝ, (fun u' : ℝ => fsh 0 u') u = (fun u' : ℝ => f s₀ u') u := by
      intro u; rw [hfsh]; simp
    have hsh_velT_fun : (fun u : ℝ => fsh 0 u) = (fun u : ℝ => f s₀ u) := by
      funext u; rw [hfsh]; simp
    rw [hsh_velT_fun]
    rw [mul_div_mul_left _ _ (by norm_num : (2 : ℝ) ≠ 0)]
  rw [intervalIntegral.integral_congr hintegrand_eq] at hS2
  exact hS2

end Variation
end Riemannian
end Geometry
end DifferentialGeometry

end
