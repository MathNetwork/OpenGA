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
import DifferentialGeometry.Geometry.Comparison.Variation.RegularParameterFirstVariation



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

def indexFormIntegrand [Module.Finite ℝ E] [IsManifold I ∞ M]
    (g : SmoothRiemannianMetric I M)
    (γ : ℝ → M) (V W : ∀ t, TangentSpace I (γ t)) (t : ℝ) : ℝ :=
  let nablaV : TangentSpace I (γ t) :=
    DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong.covDerivAlong
      (I := I) g γ V t
  let nablaW : TangentSpace I (γ t) :=
    DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong.covDerivAlong
      (I := I) g γ W t
  let gammaPrime : TangentSpace I (γ t) := mfderiv (𝓘(ℝ, ℝ)) I γ t (1 : ℝ)
  let riem : TangentSpace I (γ t) :=
    (DifferentialGeometry.Integral.Connection.riemannOp
        (DifferentialGeometry.Integral.Connection.LeviCivita
          (I := I) g) (γ t))
      (V t) gammaPrime gammaPrime
  g.inner (γ t) nablaV nablaW - g.inner (γ t) riem (W t)

def indexForm (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (a b : ℝ) (V W : ∀ t, TangentSpace I (γ t)) : ℝ :=
  ∫ t in a..b, indexFormIntegrand (I := I) g γ V W t

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
lemma indexForm_eq_intervalIntegral
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (a b : ℝ) (V W : ∀ t, TangentSpace I (γ t)) :
    indexForm (I := I) g γ a b V W =
      ∫ t in a..b, indexFormIntegrand (I := I) g γ V W t := rfl

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma continuousOn_g_inner_along_curve
    (g : SmoothRiemannianMetric I M)
    {γ : ℝ → M} {v w : ∀ t : ℝ, TangentSpace I (γ t)} {s : Set ℝ}
    (hv : ContinuousOn (fun t : ℝ => TotalSpace.mk' E
      (E := (TangentSpace I : M → Type _)) (γ t) (v t)) s)
    (hw : ContinuousOn (fun t : ℝ => TotalSpace.mk' E
      (E := (TangentSpace I : M → Type _)) (γ t) (w t)) s) :
    ContinuousOn (fun t : ℝ => g.inner (γ t) (v t) (w t)) s := by
  letI cg : Bundle.ContinuousRiemannianMetric E (TangentSpace I : M → Type _) :=
    g.toContinuousRiemannianMetric
  letI rb : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨cg.toRiemannianMetric⟩
  have h := ContinuousOn.inner_bundle (F := E) (B := M)
    (E := (TangentSpace I : M → Type _)) (b := γ) (v := v) (w := w)
    (s := s) hv hw
  refine h.congr ?_
  intro t _ht
  rfl

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 4000000 in

theorem second_variation_of_arcLength_eq_indexForm
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M) (f : ℝ → ℝ → M) (L : ℝ)
    (V : ℝ → E)
    (hf : IsSmoothVariation (I := I) f) (hL : 0 < L)
    (hγ : IsGeodesicOn (I := I) g γ (Set.Icc 0 L)) (hfc : ∀ t : ℝ, f 0 t = γ t)
    (hVeq : ∀ t : ℝ, V t = mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f u t) 0 (1 : ℝ))
    (hUnit : ∀ t ∈ Set.Icc (0 : ℝ) L,
      g.inner (γ t)
          (mfderiv (𝓘(ℝ, ℝ)) I γ t (1 : ℝ))
          (mfderiv (𝓘(ℝ, ℝ)) I γ t (1 : ℝ)) = 1)
    (hfix0 : ∀ s : ℝ, f s 0 = γ 0) (hfixL : ∀ s : ℝ, f s L = γ L)
    (hVperp : ∀ t ∈ Set.Icc (0 : ℝ) L,
      g.inner (γ t) (V t) (mfderiv (𝓘(ℝ, ℝ)) I γ t (1 : ℝ)) = 0) :
    HasDerivAt
      (fun s : ℝ => deriv
        (fun s' : ℝ => arcLength (I := I) g (fun t : ℝ => f s' t) 0 L) s)
      (indexForm (I := I) g γ 0 L V V) 0 := by
  classical
  open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong in
  have hfγ : (fun v : ℝ => f 0 v) = γ := by funext v; exact hfc v
  have hpos0 : ∀ t ∈ Set.Icc (0 : ℝ) L, 0 < speedSq (I := I) g f 0 t := by
    intro t ht
    have hu : speedSq (I := I) g f 0 t = 1 := by
      have hU := hUnit t ht
      change g.inner (f 0 t) (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f 0 u) t (1 : ℝ))
          (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f 0 u) t (1 : ℝ)) = 1
      rw [show (fun u : ℝ => f 0 u) = γ from hfγ, hfc t]
      exact hU
    rw [hu]; exact one_pos
  obtain ⟨δ, hδpos, c0, hc0, hposnear⟩ :=
    speed_positivity_near (I := I) (M := M) g f L 0 hf hpos0
  set velT : ℝ → ℝ → E := fun s t : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f s u) t (1 : ℝ)
    with hvelT
  set g₁ : ℝ → ℝ := fun s : ℝ =>
    ∫ t in (0 : ℝ)..L,
      g.inner (f s t)
        (covDerivAlong (I := I) g (fun s' : ℝ => f s' t)
          (fun s' : ℝ => velT s' t) s)
        (velT s t)
      / Real.sqrt (speedSq (I := I) g f s t) with hg₁
  have hderiv_eq : ∀ s ∈ Set.Ioo (-δ) δ,
      deriv (fun s' : ℝ => arcLength (I := I) g (fun t : ℝ => f s' t) 0 L) s = g₁ s := by
    intro s hs
    have hpos_s : ∀ t ∈ Set.Icc (0 : ℝ) L, 0 < speedSq (I := I) g f s t := by
      intro t ht
      have hc : c0 ≤ Real.sqrt (speedSq (I := I) g f s t) :=
        hposnear s (by
          rcases hs with ⟨h1, h2⟩
          exact ⟨by linarith, by linarith⟩) t ht
      have hsqrt_pos : 0 < Real.sqrt (speedSq (I := I) g f s t) := by linarith
      exact (Real.sqrt_pos.mp hsqrt_pos)
    have hfv := first_variation_of_arcLength_at_regular_parameter (I := I) g f L s hf hL hpos_s
    rw [hfv.deriv]
  set G : ℝ × ℝ → ℝ := fun p : ℝ × ℝ => speedSq (I := I) g f p.1 p.2 with hG
  have hGcdiff : ContDiff ℝ (7 : ℕ) G := speedSq_contDiff (I := I) (M := M) g f hf
  set P : ℝ × ℝ → ℝ := fun p : ℝ × ℝ =>
    fderiv ℝ (fun q : ℝ × ℝ => Real.sqrt (G q)) p (1, 0) with hP
  set Q : ℝ × ℝ → ℝ := fun p : ℝ × ℝ => fderiv ℝ P p (1, 0) with hQ
  have hg₁_deriv : HasDerivAt g₁ (indexForm (I := I) g γ 0 L V V) 0 := by
    set δ' : ℝ := δ / 2 with hδ'
    have hδ'pos : 0 < δ' := by positivity
    have hδ'lt : δ' < δ := by simp only [hδ']; linarith
    have hGpos_box : ∀ s ∈ Set.Icc (-δ') δ', ∀ t ∈ Set.Icc (0 : ℝ) L, 0 < G (s, t) := by
      intro s hs t ht
      have hc : c0 ≤ Real.sqrt (speedSq (I := I) g f s t) :=
        hposnear s (by rcases hs with ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩) t ht
      have : 0 < Real.sqrt (speedSq (I := I) g f s t) := by linarith
      exact Real.sqrt_pos.mp this
    have hΨP : ∀ s t : ℝ, 0 < G (s, t) →
        g.inner (f s t)
            (covDerivAlong (I := I) g (fun s' : ℝ => f s' t)
              (fun s' : ℝ => velT s' t) s) (velT s t)
          / Real.sqrt (speedSq (I := I) g f s t)
        = P (s, t) := by
      intro s t hpos
      have hGslice : HasDerivAt (fun u : ℝ => G (u, t))
          (fderiv ℝ G (s, t) (1, 0)) s := by
        have := Aux2.hasDerivAt_slice_fst (fun u v : ℝ => G (u, v)) s t
          ((hGcdiff.differentiable (by simp)).differentiableAt)
        simpa using this
      set fsh : ℝ → ℝ → M := fun a b : ℝ => f (s + a) b with hfsh
      have hfsh_smooth : IsSmoothVariation (I := I) fsh := by
        have hshift : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (8 : ℕ)
            (fun q : ℝ × ℝ => (s + q.1, q.2)) :=
          (contMDiff_const.add contMDiff_fst).prodMk contMDiff_snd
        exact (hf : ContMDiff _ _ _ _).comp hshift
      have hS1 := speedSq_hasDerivAt (I := I) g fsh t hfsh_smooth
      have hspeed_shift : ∀ a : ℝ, speedSq (I := I) g fsh a t
          = speedSq (I := I) g f (s + a) t := fun a => rfl
      have hS1' : HasDerivAt (fun a : ℝ => G ((s + a), t))
          (2 * g.inner (fsh 0 t)
            (covDerivAlong (I := I) g (fun a : ℝ => fsh a t)
              (fun a : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => fsh a u) t (1 : ℝ)) 0)
            (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => fsh 0 u) t (1 : ℝ))) 0 := by
        have heq : (fun a : ℝ => speedSq (I := I) g fsh a t)
            = (fun a : ℝ => G ((s + a), t)) := by
          funext a; rw [hspeed_shift a]
        rw [heq] at hS1; exact hS1
      have hGsh : HasDerivAt (fun a : ℝ => G ((s + a), t)) (fderiv ℝ G (s, t) (1, 0)) 0 := by
        have hshift : HasDerivAt (fun a : ℝ => s + a) (1 : ℝ) 0 := by
          simpa using (hasDerivAt_id (0 : ℝ)).const_add s
        have hslice0 : HasDerivAt (fun u : ℝ => G (u, t)) (fderiv ℝ G (s, t) (1, 0)) (s + 0) := by
          rw [add_zero]; exact hGslice
        have hcomp := hslice0.comp 0 hshift
        simpa using hcomp
      have hGval := hGsh.unique hS1'
      have hfoot0 : fsh 0 t = f s t := by rw [hfsh]; simp
      have hcov_shift :
          covDerivAlong (I := I) g (fun a : ℝ => fsh a t)
              (fun a : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => fsh a u) t (1 : ℝ)) 0
            = covDerivAlong (I := I) g (fun s' : ℝ => f s' t)
              (fun s' : ℝ => velT s' t) s :=
        covDerivAlong_const_add_shift (I := I) g (fun s' : ℝ => f s' t)
          (fun s' : ℝ => velT s' t) s
      have hsh_velT_fun : (fun u : ℝ => fsh 0 u) = (fun u : ℝ => f s u) := by
        funext u; rw [hfsh]; simp
      have hPval : P (s, t) = fderiv ℝ G (s, t) (1, 0) / (2 * Real.sqrt (G (s, t))) := by
        have hsqrt_slice : HasDerivAt (fun u : ℝ => Real.sqrt (G (u, t)))
            (fderiv ℝ G (s, t) (1, 0) / (2 * Real.sqrt (G (s, t)))) s :=
          hGslice.sqrt (ne_of_gt hpos)
        have hP_isfderiv : HasDerivAt (fun u : ℝ => Real.sqrt (G (u, t))) (P (s, t)) s := by
          have hslicediff : DifferentiableAt ℝ
              (fun p : ℝ × ℝ => Real.sqrt (G p)) (s, t) :=
            ((hGcdiff.contDiffAt (x := (s, t))).sqrt (ne_of_gt hpos)).differentiableAt (by simp)
          have := Aux2.hasDerivAt_slice_fst (fun u v : ℝ => Real.sqrt (G (u, v))) s t hslicediff
          simpa [hP] using this
        exact hP_isfderiv.unique hsqrt_slice
      rw [hPval, hGval, hfoot0, hcov_shift, hsh_velT_fun]
      have hspeedeq : speedSq (I := I) g f s t = G (s, t) := rfl
      rw [hspeedeq]
      change g.inner (f s t) (covDerivAlong (I := I) g (fun s' : ℝ => f s' t)
              (fun s' : ℝ => velT s' t) s)
            (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f s u) t (1 : ℝ)) / Real.sqrt (G (s, t))
          = (2 * (g.inner (f s t) (covDerivAlong (I := I) g (fun s' : ℝ => f s' t)
              (fun s' : ℝ => velT s' t) s)
            (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f s u) t (1 : ℝ))))
            / (2 * Real.sqrt (G (s, t)))
      rw [mul_div_mul_left _ _ (by norm_num : (2 : ℝ) ≠ 0)]
    set U : Set (ℝ × ℝ) := {p : ℝ × ℝ | 0 < G p} with hU
    have hUopen : IsOpen U := isOpen_lt continuous_const hGcdiff.continuous
    have hsqrtG_on : ContDiffOn ℝ (7 : ℕ) (fun p : ℝ × ℝ => Real.sqrt (G p)) U :=
      hGcdiff.contDiffOn.sqrt (fun p hp => ne_of_gt hp)
    have hP_cdiff : ContDiffOn ℝ (6 : ℕ) P U := by
      have hfdw := hsqrtG_on.fderivWithin (m := (6 : ℕ)) hUopen.uniqueDiffOn
        (by exact_mod_cast (by norm_num : (6 : ℕ) + 1 ≤ 7))
      have hP_eq : Set.EqOn P
          (fun p : ℝ × ℝ =>
            fderivWithin ℝ (fun q : ℝ × ℝ => Real.sqrt (G q)) U p (1, 0)) U := by
        intro p hp
        simp only [hP, fderivWithin_of_isOpen hUopen hp]
      exact (hfdw.clm_apply contDiffOn_const).congr hP_eq
    have hP_contOn : ContinuousOn P U := hP_cdiff.continuousOn
    have hQ_contOn : ContinuousOn Q U := by
      have hfdw := hP_cdiff.fderivWithin (m := (5 : ℕ)) hUopen.uniqueDiffOn
        (by exact_mod_cast (by norm_num : (5 : ℕ) + 1 ≤ 6))
      have hQ_eq : Set.EqOn Q
          (fun p : ℝ × ℝ => fderivWithin ℝ P U p (1, 0)) U := by
        intro p hp
        simp only [hQ, fderivWithin_of_isOpen hUopen hp]
      exact ((hfdw.clm_apply contDiffOn_const).continuousOn).congr hQ_eq
    have hbox_sub_U : Set.Icc (-δ') δ' ×ˢ Set.Icc (0 : ℝ) L ⊆ U := by
      rintro ⟨s, t⟩ ⟨hs, ht⟩
      exact hGpos_box s hs t ht
    have hP_slice_deriv : ∀ s ∈ Set.Ioo (-δ') δ', ∀ t ∈ Set.Icc (0 : ℝ) L,
        HasDerivAt (fun u : ℝ => P (u, t)) (Q (s, t)) s := by
      intro s hs t ht
      have hsU : (s, t) ∈ U :=
        hGpos_box s ⟨le_of_lt hs.1, le_of_lt hs.2⟩ t ht
      have hPdiffAt : DifferentiableAt ℝ P (s, t) :=
        ((hP_cdiff.differentiableOn (by norm_cast)).differentiableAt
          (hUopen.mem_nhds hsU))
      have := Aux2.hasDerivAt_slice_fst (fun u v : ℝ => P (u, v)) s t hPdiffAt
      simpa [hQ] using this
    set Kset : Set (ℝ × ℝ) := Set.Icc (-δ') δ' ×ˢ Set.Icc (0 : ℝ) L with hKset
    have hKcompact : IsCompact Kset := (isCompact_Icc).prod isCompact_Icc
    have hKne : Kset.Nonempty :=
      ⟨(0, 0), ⟨⟨by linarith, by linarith⟩, ⟨le_refl 0, le_of_lt hL⟩⟩⟩
    have hQ_contOn_box : ContinuousOn (fun p : ℝ × ℝ => ‖Q p‖) Kset :=
      (continuous_norm.comp_continuousOn (hQ_contOn.mono hbox_sub_U))
    obtain ⟨pm, hpmKset, hpmMax⟩ := hKcompact.exists_isMaxOn hKne hQ_contOn_box
    set K2 : ℝ := ‖Q pm‖ with hK2
    have hK2nonneg : 0 ≤ K2 := norm_nonneg _
    have hP_slice_contOn : ∀ s ∈ Set.Icc (-δ') δ',
        ContinuousOn (fun t : ℝ => P (s, t)) (Set.Icc (0 : ℝ) L) := by
      intro s hs
      have hmap : ∀ t ∈ Set.Icc (0 : ℝ) L, (s, t) ∈ U := fun t ht => hGpos_box s hs t ht
      exact (hP_contOn.comp (continuous_const.prodMk continuous_id).continuousOn hmap)
    have hQ_slice_contOn : ∀ s ∈ Set.Icc (-δ') δ',
        ContinuousOn (fun t : ℝ => Q (s, t)) (Set.Icc (0 : ℝ) L) := by
      intro s hs
      have hmap : ∀ t ∈ Set.Icc (0 : ℝ) L, (s, t) ∈ U := fun t ht => hGpos_box s hs t ht
      exact (hQ_contOn.comp (continuous_const.prodMk continuous_id).continuousOn hmap)
    have hH1 := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume) (a := (0 : ℝ)) (b := L)
      (F := fun s t => P (s, t)) (F' := fun s t => Q (s, t)) (x₀ := (0 : ℝ))
      (bound := fun _ => K2) (s := Set.Ioo (-δ') δ')
      (Ioo_mem_nhds (by linarith) hδ'pos)
      (Filter.eventually_of_mem (Ioo_mem_nhds (by linarith : (-δ' : ℝ) < 0) hδ'pos)
        (fun s hs => by
          have hsIcc : s ∈ Set.Icc (-δ') δ' := ⟨le_of_lt hs.1, le_of_lt hs.2⟩
          rw [Set.uIoc_of_le (le_of_lt hL)]
          exact ((hP_slice_contOn s hsIcc).mono Set.Ioc_subset_Icc_self).aestronglyMeasurable
            measurableSet_Ioc))
      (by
        have h0box : (0 : ℝ) ∈ Set.Icc (-δ') δ' := ⟨by linarith, by linarith⟩
        exact (hP_slice_contOn 0 h0box).intervalIntegrable_of_Icc (le_of_lt hL))
      (by
        have h0box : (0 : ℝ) ∈ Set.Icc (-δ') δ' := ⟨by linarith, by linarith⟩
        rw [Set.uIoc_of_le (le_of_lt hL)]
        exact ((hQ_slice_contOn 0 h0box).mono Set.Ioc_subset_Icc_self).aestronglyMeasurable
          measurableSet_Ioc)
      (by
        apply Filter.Eventually.of_forall
        intro t ht s hs
        rw [Set.uIoc_of_le (le_of_lt hL)] at ht
        have htIcc : t ∈ Set.Icc (0 : ℝ) L := ⟨le_of_lt ht.1, ht.2⟩
        have hsIcc : s ∈ Set.Icc (-δ') δ' := ⟨le_of_lt hs.1, le_of_lt hs.2⟩
        have hpKset : (s, t) ∈ Kset := ⟨hsIcc, htIcc⟩
        exact hpmMax hpKset)
      (_root_.intervalIntegrable_const)
      (by
        apply Filter.Eventually.of_forall
        intro t ht s hs
        rw [Set.uIoc_of_le (le_of_lt hL)] at ht
        have htIcc : t ∈ Set.Icc (0 : ℝ) L := ⟨le_of_lt ht.1, ht.2⟩
        exact hP_slice_deriv s hs t htIcc)
    have hg₁_eq : g₁ =ᶠ[nhds (0 : ℝ)]
        (fun s : ℝ => ∫ t in (0 : ℝ)..L, P (s, t)) := by
      refine Filter.eventually_of_mem (Ioo_mem_nhds (by linarith : (-δ' : ℝ) < 0) hδ'pos)
        (fun s hs => ?_)
      have hsIcc : s ∈ Set.Icc (-δ') δ' := ⟨le_of_lt hs.1, le_of_lt hs.2⟩
      refine intervalIntegral.integral_congr (fun t ht => ?_)
      rw [Set.uIcc_of_le (le_of_lt hL)] at ht
      exact hΨP s t (hGpos_box s hsIcc t ht)
    have hg₁_H1 : HasDerivAt g₁ (∫ t in (0 : ℝ)..L, Q (0, t)) 0 :=
      hH1.2.congr_of_eventuallyEq hg₁_eq
    set γ' : ∀ t : ℝ, TangentSpace I (γ t) := fun t : ℝ => mfderiv (𝓘(ℝ, ℝ)) I γ t (1 : ℝ)
      with hγ'def
    have hγ_smooth : ContMDiff (𝓘(ℝ, ℝ)) I (8 : ℕ) γ := by
      have hsmooth_central : ContMDiff (𝓘(ℝ, ℝ)) I (8 : ℕ) (fun v : ℝ => f 0 v) := by
        have hincl : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (8 : ℕ) (fun v : ℝ => ((0 : ℝ), v)) :=
          contMDiff_const.prodMk contMDiff_id
        exact (hf : ContMDiff _ _ _ _).comp hincl
      exact hfγ ▸ hsmooth_central
    set g_s : ℝ → ℝ := fun t : ℝ => fderiv ℝ G (0, t) (1, 0) with hg_sdef
    set g_ss : ℝ → ℝ := fun t : ℝ => fderiv ℝ (fun p : ℝ × ℝ => fderiv ℝ G p (1, 0)) (0, t) (1, 0)
      with hg_ssdef
    have hG01 : ∀ t ∈ Set.Icc (0 : ℝ) L, G (0, t) = 1 := by
      intro t ht
      change g.inner (f 0 t) (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f 0 u) t (1 : ℝ))
          (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f 0 u) t (1 : ℝ)) = 1
      rw [show (fun u : ℝ => f 0 u) = γ from hfγ, hfc t]
      exact hUnit t ht
    set Vsec : ∀ t : ℝ, TangentSpace I (γ t) :=
      fun t : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f u t) 0 (1 : ℝ) with hVsecdef
    have hVsec_eq : ∀ t : ℝ, Vsec t = V t := fun t => (hVeq t).symm
    have hVdiff : ∀ t₀ : ℝ, DifferentiableAt ℝ (chartRepAt (I := I) γ Vsec t₀) t₀ := by
      intro t₀
      have h := variationField_chartRep_differentiableAt (I := I) g f hf t₀
      have hfun : (fun v : ℝ => f 0 v) = γ := hfγ
      rw [show (fun v : ℝ => f 0 v) = γ from hfγ] at h
      exact h
    have hγ'diff : ∀ t₀ : ℝ, DifferentiableAt ℝ (chartRepAt (I := I) γ γ' t₀) t₀ := by
      intro t₀
      have h := velocityField_chartRep_differentiableAt (I := I) g f hf t₀
      rw [show (fun v : ℝ => f 0 v) = γ from hfγ] at h
      exact h
    have hgeo0 : ∀ t ∈ Set.Icc (0 : ℝ) L, covDerivAlong (I := I) g γ γ' t = 0 := by
      intro t ht
      have hgeo : HasGeodesicEquationAt (I := I) g γ t := hγ t ht
      exact covDerivAlong_velocity_eq_zero_of_hasGeodesicEquationAt_C2 (I := I) g γ t
        (hγ_smooth.contMDiffAt.of_le (by exact_mod_cast (by norm_num : (2 : ℕ) ≤ 8))) hgeo
    have hVnabperp : ∀ t ∈ Set.Icc (0 : ℝ) L,
        g.inner (γ t) (covDerivAlong (I := I) g γ Vsec t) (γ' t) = 0 := by
      intro t ht
      have hderiv0 : HasDerivWithinAt (fun s : ℝ => g.inner (γ s) (Vsec s) (γ' s)) 0
          (Set.Icc 0 L) t := by
        refine (hasDerivWithinAt_const t (Set.Icc 0 L) (0 : ℝ)).congr_of_mem ?_ ht
        intro s hs
        rw [hVsec_eq s]; exact hVperp s hs
      have hmc := metric_compat_hasDerivAt_inner (I := I) (by exact_mod_cast (by norm_num : (1 : ℕ) ≤ 8)) g γ Vsec γ' t hγ_smooth
        (hVdiff t) (hγ'diff t)
      have hmcWithin : HasDerivWithinAt (fun s : ℝ => g.inner (γ s) (Vsec s) (γ' s))
          (g.inner (γ t) (covDerivAlong (I := I) g γ Vsec t) (γ' t)
            + g.inner (γ t) (Vsec t) (covDerivAlong (I := I) g γ γ' t)) (Set.Icc 0 L) t :=
        hmc.hasDerivWithinAt
      have huniq := (uniqueDiffOn_Icc hL t ht).eq_deriv (Set.Icc 0 L) hderiv0 hmcWithin
      have hB : g.inner (γ t) (Vsec t) (covDerivAlong (I := I) g γ γ' t) = 0 := by
        rw [hgeo0 t ht]
        simp
      rw [hB, add_zero] at huniq
      exact huniq.symm
    have hgs_eq : ∀ t : ℝ,
        g_s t = 2 * g.inner (γ t) (covDerivAlong (I := I) g γ Vsec t) (γ' t) := by
      intro t
      have hS1 := speedSq_hasDerivAt (I := I) g f t hf
      have hGslice : HasDerivAt (fun u : ℝ => G (u, t)) (g_s t) 0 := by
        have := Aux2.hasDerivAt_slice_fst (fun u v : ℝ => G (u, v)) 0 t
          ((hGcdiff.differentiable (by simp)).differentiableAt)
        simpa [hg_sdef] using this
      have hS1' : HasDerivAt (fun u : ℝ => G (u, t))
          (2 * g.inner (f 0 t)
            (covDerivAlong (I := I) g (fun s : ℝ => f s t)
              (fun s : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f s u) t (1 : ℝ)) 0)
            (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f 0 u) t (1 : ℝ))) 0 := hS1
      have huniq := hGslice.unique hS1'
      rw [huniq]
      have hcomm := commute_ds_dt_intrinsic (I := I) g f hf t
      have hcov : covDerivAlong (I := I) g (fun s : ℝ => f s t)
            (fun s : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f s u) t (1 : ℝ)) 0
          = covDerivAlong (I := I) g γ Vsec t := by
        rw [hcomm, show (fun v : ℝ => f 0 v) = γ from hfγ]
      rw [hcov]
      rw [hfc t]
      have hvel : (fun u : ℝ => f 0 u) = γ := hfγ
      rw [hvel]
    have hgs0 : ∀ t ∈ Set.Icc (0 : ℝ) L, g_s t = 0 := by
      intro t ht
      rw [hgs_eq t, hVnabperp t ht, mul_zero]
    have h0mem : (0 : ℝ) ∈ Set.Ioo (-δ') δ' := ⟨by linarith, hδ'pos⟩
    have hQpt : ∀ t ∈ Set.Icc (0 : ℝ) L, Q (0, t) = g_ss t / 2 := by
      intro t ht
      have hG0 : G (0, t) = 1 := hG01 t ht
      have hsqrt0 : Real.sqrt (G (0, t)) = 1 := by rw [hG0, Real.sqrt_one]
      have hPderiv : HasDerivAt (fun u : ℝ => P (u, t)) (Q (0, t)) 0 :=
        hP_slice_deriv 0 h0mem t ht
      have hsqrtderiv : HasDerivAt (fun u : ℝ => Real.sqrt (G (u, t))) (P (0, t)) 0 := by
        have hGslice : HasDerivAt (fun u : ℝ => G (u, t)) (fderiv ℝ G (0, t) (1, 0)) 0 := by
          have := Aux2.hasDerivAt_slice_fst (fun u v : ℝ => G (u, v)) 0 t
            ((hGcdiff.differentiable (by simp)).differentiableAt)
          simpa using this
        have := hGslice.sqrt (by rw [hG0]; norm_num)
        have hPeq : P (0, t) = fderiv ℝ G (0, t) (1, 0) / (2 * Real.sqrt (G (0, t))) := by
          have hslicediff : DifferentiableAt ℝ (fun p : ℝ × ℝ => Real.sqrt (G p)) (0, t) :=
            ((hGcdiff.contDiffAt (x := (0, t))).sqrt (by rw [hG0]; norm_num)).differentiableAt
              (by simp)
          have hslice := Aux2.hasDerivAt_slice_fst (fun u v : ℝ => Real.sqrt (G (u, v))) 0 t
            hslicediff
          have : P (0, t) = fderiv ℝ (fun p : ℝ × ℝ => Real.sqrt (G p)) (0, t) (1, 0) := rfl
          rw [this]
          exact (Aux2.hasDerivAt_slice_fst (fun u v : ℝ => Real.sqrt (G (u, v))) 0 t hslicediff).unique
            (hGslice.sqrt (by rw [hG0]; norm_num))
        rw [hPeq]; exact this
      have hP0 : P (0, t) = 0 := by
        have hgs : g_s t = 0 := hgs0 t ht
        have : P (0, t) = fderiv ℝ G (0, t) (1, 0) / (2 * Real.sqrt (G (0, t))) := by
          have hslicediff : DifferentiableAt ℝ (fun p : ℝ × ℝ => Real.sqrt (G p)) (0, t) :=
            ((hGcdiff.contDiffAt (x := (0, t))).sqrt (by rw [hG0]; norm_num)).differentiableAt
              (by simp)
          have hGslice : HasDerivAt (fun u : ℝ => G (u, t)) (fderiv ℝ G (0, t) (1, 0)) 0 := by
            have := Aux2.hasDerivAt_slice_fst (fun u v : ℝ => G (u, v)) 0 t
              ((hGcdiff.differentiable (by simp)).differentiableAt)
            simpa using this
          have hPis : P (0, t) = fderiv ℝ (fun p : ℝ × ℝ => Real.sqrt (G p)) (0, t) (1, 0) := rfl
          rw [hPis]
          exact (Aux2.hasDerivAt_slice_fst (fun u v : ℝ => Real.sqrt (G (u, v))) 0 t hslicediff).unique
            (hGslice.sqrt (by rw [hG0]; norm_num))
        rw [this]
        have : fderiv ℝ G (0, t) (1, 0) = 0 := hgs
        rw [this]; simp
      have hLHS : HasDerivAt (fun s : ℝ => 2 * (P (s, t) * Real.sqrt (G (s, t))))
          (2 * Q (0, t)) 0 := by
        have hprod := hPderiv.mul hsqrtderiv
        have hprod' : HasDerivAt (fun s : ℝ => P (s, t) * Real.sqrt (G (s, t)))
            (Q (0, t)) 0 := by
          have heq : Q (0, t) * Real.sqrt (G (0, t)) + P (0, t) * P (0, t) = Q (0, t) := by
            rw [hsqrt0, hP0]; ring
          rw [← heq]; exact hprod
        have := hprod'.const_mul (2 : ℝ)
        exact this
      have hRHS : HasDerivAt (fun s : ℝ => fderiv ℝ G (s, t) (1, 0)) (g_ss t) 0 := by
        have hslicediff : DifferentiableAt ℝ
            (fun p : ℝ × ℝ => fderiv ℝ G p (1, 0)) (0, t) := by
          have hfd : ContDiff ℝ (6 : ℕ) (fun p : ℝ × ℝ => fderiv ℝ G p) :=
            hGcdiff.fderiv_right (by exact_mod_cast (by norm_num : (6 : ℕ) + 1 ≤ 7))
          have hfdapp : ContDiff ℝ (6 : ℕ) (fun p : ℝ × ℝ => fderiv ℝ G p (1, 0)) :=
            (ContinuousLinearMap.apply ℝ ℝ ((1, 0) : ℝ × ℝ)).contDiff.comp hfd
          exact (hfdapp.differentiable (by norm_num)).differentiableAt
        have := Aux2.hasDerivAt_slice_fst (fun u v : ℝ => fderiv ℝ G (u, v) (1, 0)) 0 t hslicediff
        simpa [hg_ssdef] using this
      have hagree : (fun s : ℝ => 2 * (P (s, t) * Real.sqrt (G (s, t))))
          =ᶠ[nhds (0 : ℝ)] (fun s : ℝ => fderiv ℝ G (s, t) (1, 0)) := by
        refine Filter.eventually_of_mem (Ioo_mem_nhds (by linarith : (-δ' : ℝ) < 0) hδ'pos)
          (fun s hs => ?_)
        simp only []
        have hsIcc : s ∈ Set.Icc (-δ') δ' := ⟨le_of_lt hs.1, le_of_lt hs.2⟩
        have hGpos : 0 < G (s, t) := hGpos_box s hsIcc t ht
        have hPeq : P (s, t) = fderiv ℝ G (s, t) (1, 0) / (2 * Real.sqrt (G (s, t))) := by
          have hslicediff : DifferentiableAt ℝ (fun p : ℝ × ℝ => Real.sqrt (G p)) (s, t) :=
            ((hGcdiff.contDiffAt (x := (s, t))).sqrt (ne_of_gt hGpos)).differentiableAt (by simp)
          have hGslice : HasDerivAt (fun u : ℝ => G (u, t)) (fderiv ℝ G (s, t) (1, 0)) s := by
            have := Aux2.hasDerivAt_slice_fst (fun u v : ℝ => G (u, v)) s t
              ((hGcdiff.differentiable (by simp)).differentiableAt)
            simpa using this
          have hPis : P (s, t) = fderiv ℝ (fun p : ℝ × ℝ => Real.sqrt (G p)) (s, t) (1, 0) := rfl
          rw [hPis]
          exact (Aux2.hasDerivAt_slice_fst (fun u v : ℝ => Real.sqrt (G (u, v))) s t hslicediff).unique
            (hGslice.sqrt (ne_of_gt hGpos))
        rw [hPeq]
        have hsqrtne : Real.sqrt (G (s, t)) ≠ 0 := by
          rw [Real.sqrt_ne_zero (le_of_lt hGpos)]; exact ne_of_gt hGpos
        field_simp
      have h2Q : 2 * Q (0, t) = g_ss t :=
        (hLHS.congr_of_eventuallyEq hagree.symm).unique hRHS
      linarith
    set W2 : ∀ t : ℝ, TangentSpace I (γ t) := fun t : ℝ =>
      covDerivAlong (I := I) g (fun s : ℝ => f s t)
        (fun s : ℝ => covDerivAlong (I := I) g (fun s' : ℝ => f s' t)
          (fun s' : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f s' w) t (1 : ℝ)) s) 0 with hW2def
    have hgss_pt : ∀ t ∈ Set.Icc (0 : ℝ) L,
        g_ss t / 2 = g.inner (γ t) (W2 t) (γ' t)
          + g.inner (γ t) (covDerivAlong (I := I) g γ Vsec t)
            (covDerivAlong (I := I) g γ Vsec t) := by
      intro t ht
      set c : ℝ → M := fun s : ℝ => f s t with hc
      set velTsec : ∀ s : ℝ, TangentSpace I (c s) := fun s : ℝ =>
        mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f s w) t (1 : ℝ) with hvelTsec
      set Wsec : ∀ s : ℝ, TangentSpace I (c s) := fun s : ℝ =>
        covDerivAlong (I := I) g (fun s' : ℝ => f s' t)
          (fun s' : ℝ => velTsec s') s with hWsec
      have hc_smooth : ContMDiff (𝓘(ℝ, ℝ)) I (8 : ℕ) c := by
        have hincl : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (8 : ℕ) (fun s : ℝ => (s, t)) :=
          contMDiff_id.prodMk contMDiff_const
        exact (hf : ContMDiff _ _ _ _).comp hincl
      have hc0 : c 0 = γ t := by rw [hc]; exact hfc t
      have hvelTdiff : DifferentiableAt ℝ (chartRepAt (I := I) c velTsec 0) 0 := by
        have := slice_longitudinalField_transverse_chartRep_differentiableAt (I := I) g f hf t
        exact this
      have hWdiff : DifferentiableAt ℝ (chartRepAt (I := I) c Wsec 0) 0 :=
        slice_secondCovDeriv_chartRep_differentiableAt (I := I) g f hf t
      have hmc := metric_compat_hasDerivAt_inner (I := I) (by exact_mod_cast (by norm_num : (1 : ℕ) ≤ 8)) g c Wsec velTsec 0
        hc_smooth hWdiff hvelTdiff
      have hcovW : covDerivAlong (I := I) g c Wsec 0 = W2 t := by
        rw [hW2def, hc, hWsec, hvelTsec]
      have hcomm := commute_ds_dt_intrinsic (I := I) g f hf t
      have hcomm' : covDerivAlong (I := I) g (fun s' : ℝ => f s' t)
            (fun s' : ℝ => velTsec s') 0
          = covDerivAlong (I := I) g γ Vsec t := by
        rw [hvelTsec]
        rw [hcomm]
        have hfγ' : (fun v : ℝ => f 0 v) = γ := hfγ
        rw [hfγ']
      have hcovVel : covDerivAlong (I := I) g c velTsec 0
          = covDerivAlong (I := I) g γ Vsec t := by rw [hc]; exact hcomm'
      have hWval : Wsec 0 = covDerivAlong (I := I) g γ Vsec t := by
        rw [hWsec]; exact hcomm'
      have hvelval : velTsec 0 = γ' t := by
        change mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f 0 w) t (1 : ℝ) = γ' t
        have hfγ' : (fun w : ℝ => f 0 w) = γ := hfγ
        rw [hfγ']
        rfl
      have hmc' : HasDerivAt (fun s : ℝ => g.inner (c s) (Wsec s) (velTsec s))
          (g.inner (γ t) (W2 t) (γ' t)
            + g.inner (γ t) (covDerivAlong (I := I) g γ Vsec t)
              (covDerivAlong (I := I) g γ Vsec t)) 0 := by
        have := hmc
        rw [hcovW, hcovVel, hWval, hvelval, hc0] at this
        exact this
      have hpartial_eq : (fun s : ℝ => fderiv ℝ G (s, t) (1, 0))
          = (fun s : ℝ => 2 * g.inner (c s) (Wsec s) (velTsec s)) := by
        funext s
        set fsh : ℝ → ℝ → M := fun a b : ℝ => f (s + a) b with hfsh
        have hfsh_smooth : IsSmoothVariation (I := I) fsh := by
          have hshift : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (8 : ℕ)
              (fun q : ℝ × ℝ => (s + q.1, q.2)) :=
            (contMDiff_const.add contMDiff_fst).prodMk contMDiff_snd
          exact (hf : ContMDiff _ _ _ _).comp hshift
        have hS1 := speedSq_hasDerivAt (I := I) g fsh t hfsh_smooth
        have hspeed_shift : ∀ a : ℝ, speedSq (I := I) g fsh a t
            = speedSq (I := I) g f (s + a) t := fun a => rfl
        have hS1' : HasDerivAt (fun a : ℝ => G ((s + a), t))
            (2 * g.inner (fsh 0 t)
              (covDerivAlong (I := I) g (fun a : ℝ => fsh a t)
                (fun a : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => fsh a u) t (1 : ℝ)) 0)
              (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => fsh 0 u) t (1 : ℝ))) 0 := by
          have heq : (fun a : ℝ => speedSq (I := I) g fsh a t)
              = (fun a : ℝ => G ((s + a), t)) := by
            funext a; rw [hspeed_shift a]
          rw [heq] at hS1; exact hS1
        have hGsh : HasDerivAt (fun a : ℝ => G ((s + a), t)) (fderiv ℝ G (s, t) (1, 0)) 0 := by
          have hshift : HasDerivAt (fun a : ℝ => s + a) (1 : ℝ) 0 := by
            simpa using (hasDerivAt_id (0 : ℝ)).const_add s
          have hslice0 : HasDerivAt (fun u : ℝ => G (u, t)) (fderiv ℝ G (s, t) (1, 0)) (s + 0) := by
            rw [add_zero]
            have := Aux2.hasDerivAt_slice_fst (fun u v : ℝ => G (u, v)) s t
              ((hGcdiff.differentiable (by simp)).differentiableAt)
            simpa using this
          have hcomp := hslice0.comp 0 hshift
          simpa using hcomp
        have hGval := hGsh.unique hS1'
        have hfoot0 : fsh 0 t = c s := by rw [hfsh, hc]; simp
        have hcov_shift :
            covDerivAlong (I := I) g (fun a : ℝ => fsh a t)
                (fun a : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => fsh a u) t (1 : ℝ)) 0
              = Wsec s := by
          rw [hWsec, hvelTsec]
          exact covDerivAlong_const_add_shift (I := I) g (fun s' : ℝ => f s' t)
            (fun s' : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f s' u) t (1 : ℝ)) s
        have hsh_velT_fun : (fun u : ℝ => fsh 0 u) = (fun u : ℝ => f s u) := by
          funext u; rw [hfsh]; simp
        rw [hGval, hfoot0, hcov_shift, hsh_velT_fun]
      have hgss_deriv : HasDerivAt (fun s : ℝ => fderiv ℝ G (s, t) (1, 0)) (g_ss t) 0 := by
        have hslicediff : DifferentiableAt ℝ
            (fun p : ℝ × ℝ => fderiv ℝ G p (1, 0)) (0, t) := by
          have hfd : ContDiff ℝ (6 : ℕ) (fun p : ℝ × ℝ => fderiv ℝ G p) :=
            hGcdiff.fderiv_right (by exact_mod_cast (by norm_num : (6 : ℕ) + 1 ≤ 7))
          have hfdapp : ContDiff ℝ (6 : ℕ) (fun p : ℝ × ℝ => fderiv ℝ G p (1, 0)) :=
            (ContinuousLinearMap.apply ℝ ℝ ((1, 0) : ℝ × ℝ)).contDiff.comp hfd
          exact (hfdapp.differentiable (by norm_num)).differentiableAt
        have := Aux2.hasDerivAt_slice_fst (fun u v : ℝ => fderiv ℝ G (u, v) (1, 0)) 0 t hslicediff
        simpa [hg_ssdef] using this
      have hmc'' : HasDerivAt (fun s : ℝ => fderiv ℝ G (s, t) (1, 0))
          (2 * (g.inner (γ t) (W2 t) (γ' t)
            + g.inner (γ t) (covDerivAlong (I := I) g γ Vsec t)
              (covDerivAlong (I := I) g γ Vsec t))) 0 := by
        rw [hpartial_eq]
        have hcm := hmc'.const_mul (2 : ℝ)
        convert hcm using 1
      have huniq := hgss_deriv.unique hmc''
      rw [huniq]
      ring
    have hgss_int :
        (∫ t in (0 : ℝ)..L, g_ss t / 2) = indexForm (I := I) g γ 0 L V V := by
      set velS : ℝ → ℝ → E := fun u v : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f w v) u (1 : ℝ)
        with hvelSdef
      set velT : ℝ → ℝ → E := fun s v : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f s w) v (1 : ℝ)
        with hvelTdef
      set Asec : ∀ t : ℝ, TangentSpace I (γ t) := fun t : ℝ =>
        covDerivAlong (I := I) g (fun u : ℝ => f u t) (fun u : ℝ => velS u t) 0 with hAsecdef
      set Bsec : ∀ t : ℝ, TangentSpace I (γ t) := fun t : ℝ =>
        covDerivAlong (I := I) g γ Asec t with hBsecdef
      set Rsec : ∀ t : ℝ, TangentSpace I (γ t) := fun t : ℝ =>
        (DifferentialGeometry.Integral.Connection.riemannOp
          (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g) (γ t))
          (V t) (γ' t) (V t) with hRsecdef
      have hcurv : ∀ t : ℝ, W2 t = Bsec t + Rsec t := by
        intro t
        have houterL : DifferentiableAt ℝ (chartRepAt (I := I) (fun s : ℝ => f s t)
            (fun s : ℝ => covDerivAlong (I := I) g (fun v : ℝ => f s v)
              (fun v : ℝ => velS s v) t) 0) 0 := by
          have hsec_eq : (fun s : ℝ => covDerivAlong (I := I) g (fun v : ℝ => f s v)
              (fun v : ℝ => velS s v) t)
              = (fun s : ℝ => covDerivAlong (I := I) g (fun s' : ℝ => f s' t)
                (fun s' : ℝ => velT s' t) s) :=
            (commute_ds_dt_intrinsic_shifted (I := I) g f hf t).symm
          rw [hsec_eq]
          exact slice_secondCovDeriv_chartRep_differentiableAt (I := I) g f hf t
        have houterR : DifferentiableAt ℝ (chartRepAt (I := I) (fun v : ℝ => f 0 v)
            (fun v : ℝ => covDerivAlong (I := I) g (fun u : ℝ => f u v)
              (fun u : ℝ => velS u v) 0) t) t :=
          slice_secondCovDeriv_central_chartRep_differentiableAt (I := I) g f hf t
        have hcomm := commute_ds_dt_curvature_innerS (I := I) g f hf t houterL houterR
        have hfirst : covDerivAlong (I := I) g (fun s : ℝ => f s t)
            (fun s : ℝ => covDerivAlong (I := I) g (fun v : ℝ => f s v)
              (fun v : ℝ => velS s v) t) 0 = W2 t := by
          have hsec_eq : (fun s : ℝ => covDerivAlong (I := I) g (fun v : ℝ => f s v)
              (fun v : ℝ => velS s v) t)
              = (fun s : ℝ => covDerivAlong (I := I) g (fun s' : ℝ => f s' t)
                (fun s' : ℝ => velT s' t) s) :=
            (commute_ds_dt_intrinsic_shifted (I := I) g f hf t).symm
          rw [hsec_eq, hW2def]
        have hsecond : covDerivAlong (I := I) g (fun v : ℝ => f 0 v)
            (fun v : ℝ => covDerivAlong (I := I) g (fun u : ℝ => f u v)
              (fun u : ℝ => velS u v) 0) t = Bsec t := by
          rw [hBsecdef]
          change covDerivAlong (I := I) g (fun v : ℝ => f 0 v) Asec t
            = covDerivAlong (I := I) g γ Asec t
          rw [show (fun v : ℝ => f 0 v) = γ from hfγ]
        have hvelS0 : velS 0 t = V t := (hVeq t).symm
        have hvelT0 : velT 0 t = γ' t := by
          have h1 : velT 0 t = mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f 0 w) t (1 : ℝ) := rfl
          rw [h1, show (fun w : ℝ => f 0 w) = γ from hfγ]
          rfl
        rw [hfirst, hsecond] at hcomm
        have hVeq' : (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f u t) 0 (1 : ℝ) : E) = V t :=
          (hVeq t).symm
        have hγ'eq : (mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f 0 w) t (1 : ℝ) : E) = γ' t := by
          rw [show (fun w : ℝ => f 0 w) = γ from hfγ]; rfl
        have hfoot : f 0 t = γ t := hfc t
        have hR : (DifferentialGeometry.Integral.Connection.riemannOp
              (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g) (f 0 t))
              (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f u t) 0 (1 : ℝ))
              (mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f 0 w) t (1 : ℝ))
              (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => f u t) 0 (1 : ℝ)) = Rsec t := by
          rw [hRsecdef]
          rw [hVeq', hγ'eq]
          exact hfoot ▸ rfl
        rw [hR] at hcomm
        rw [← hcomm]; abel
      have hskew : ∀ t : ℝ, g.inner (γ t) (Rsec t) (γ' t)
          = - g.inner (γ t) ((DifferentialGeometry.Integral.Connection.riemannOp
              (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g) (γ t))
              (V t) (γ' t) (γ' t)) (V t) := by
        intro t
        have hsk := DifferentialGeometry.Integral.Connection.riemannOp_metric_skew
          (I := I) g (γ t) (V t) (γ' t) (V t) (γ' t)
        change g.inner (γ t) (Rsec t) (γ' t)
          = - g.inner (γ t) ((DifferentialGeometry.Integral.Connection.riemannOp
              (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g) (γ t))
              (V t) (γ' t) (γ' t)) (V t)
        rw [hRsecdef]
        have hsymm : g.inner (γ t) (V t) ((DifferentialGeometry.Integral.Connection.riemannOp
              (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g) (γ t))
              (V t) (γ' t) (γ' t))
            = g.inner (γ t) ((DifferentialGeometry.Integral.Connection.riemannOp
              (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g) (γ t))
              (V t) (γ' t) (γ' t)) (V t) := g.symm (γ t) _ _
        rw [hsymm] at hsk
        linarith [hsk]
      have hAsec_endpoint : ∀ t₀ : ℝ, (∀ u : ℝ, f u t₀ = γ t₀) → Asec t₀ = 0 := by
        intro t₀ hconst
        change covDerivAlong (I := I) g (fun u : ℝ => f u t₀) (fun u : ℝ => velS u t₀) 0 = 0
        have hvel0 : (fun u : ℝ => velS u t₀) = (fun _ : ℝ => (0 : E)) := by
          funext u
          change mfderiv (𝓘(ℝ, ℝ)) I (fun w : ℝ => f w t₀) u (1 : ℝ) = (0 : E)
          have hconstfun : (fun w : ℝ => f w t₀) = (fun _ : ℝ => γ t₀) := by
            funext w; exact hconst w
          rw [hconstfun, mfderiv_const]
          rfl
        rw [hvel0]
        exact covDerivAlong_zero (I := I) g (fun u : ℝ => f u t₀) 0
      have hAsec0 : Asec 0 = 0 := hAsec_endpoint 0 (fun u => hfix0 u)
      have hAsecL : Asec L = 0 := hAsec_endpoint L (fun u => hfixL u)
      have hAsecdiff : ∀ t₀ : ℝ, DifferentiableAt ℝ (chartRepAt (I := I) γ Asec t₀) t₀ := by
        intro t₀
        have h := slice_secondCovDeriv_central_chartRep_differentiableAt (I := I) g f hf t₀
        rw [show (fun v : ℝ => f 0 v) = γ from hfγ] at h
        exact h
      have hDderiv : ∀ t ∈ Set.Icc (0 : ℝ) L,
          HasDerivAt (fun s : ℝ => g.inner (γ s) (Asec s) (γ' s))
            (g.inner (γ t) (Bsec t) (γ' t)) t := by
        intro t ht
        have hmc := metric_compat_hasDerivAt_inner (I := I) (by exact_mod_cast (by norm_num : (1 : ℕ) ≤ 8)) g γ Asec γ' t hγ_smooth
          (hAsecdiff t) (hγ'diff t)
        have hB2 : g.inner (γ t) (Asec t) (covDerivAlong (I := I) g γ γ' t) = 0 := by
          rw [hgeo0 t ht]; simp
        rw [hB2, add_zero] at hmc
        exact hmc
      have hpt_id : ∀ t ∈ Set.Icc (0 : ℝ) L,
          g_ss t / 2 = indexFormIntegrand (I := I) g γ V V t
            + g.inner (γ t) (Bsec t) (γ' t) := by
        intro t ht
        rw [hgss_pt t ht]
        have hWexp : g.inner (γ t) (W2 t) (γ' t)
            = g.inner (γ t) (Bsec t) (γ' t) + g.inner (γ t) (Rsec t) (γ' t) := by
          rw [hcurv t, map_add, ContinuousLinearMap.add_apply]
        have hVsecfun : Vsec = (fun t : ℝ => V t) := by funext s; exact hVsec_eq s
        have hIFI : indexFormIntegrand (I := I) g γ V V t
            = g.inner (γ t) (covDerivAlong (I := I) g γ V t) (covDerivAlong (I := I) g γ V t)
              - g.inner (γ t)
                ((DifferentialGeometry.Integral.Connection.riemannOp
                  (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g) (γ t))
                  (V t) (γ' t) (γ' t)) (V t) := rfl
        rw [hIFI, hWexp, hskew t]
        rw [hVsecfun]
        ring
      have hγ_C1On : ContMDiffOn (𝓘(ℝ, ℝ)) I 1 γ (Set.Icc 0 L) :=
        (hγ_smooth.of_le (by exact_mod_cast (by norm_num : (1 : ℕ) ≤ 8))).contMDiffOn
      have hV_total : ContinuousOn
          (fun t : ℝ => (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
            (γ t) (V t) : TangentBundle I M)) (Set.Icc 0 L) := by
        have hsec : ContinuousOn
            (fun t : ℝ => (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
              (γ t) (Vsec t) : TangentBundle I M)) (Set.Icc 0 L) :=
          sectionAlongCurve_continuousOn_totalSpace_of_contMDiffOn (I := I) γ Vsec hγ_C1On
            (fun t _ => hVdiff t)
        refine hsec.congr (fun t _ => ?_)
        rw [hVsec_eq t]
      have hγ'_total : ContinuousOn
          (fun t : ℝ => (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
            (γ t) (γ' t) : TangentBundle I M)) (Set.Icc 0 L) :=
        sectionAlongCurve_continuousOn_totalSpace_of_contMDiffOn (I := I) γ γ' hγ_C1On
          (fun t _ => hγ'diff t)
      have hnablaV_diff : ∀ t₀ : ℝ, DifferentiableAt ℝ
          (chartRepAt (I := I) γ (covDerivAlong (I := I) g γ Vsec) t₀) t₀ := by
        intro t₀
        have h := variationField_covDeriv_chartRep_differentiableAt (I := I) g f hf t₀
        rw [show (fun v : ℝ => f 0 v) = γ from hfγ] at h
        exact h
      have hnablaV_total : ContinuousOn
          (fun t : ℝ => (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
            (γ t) (covDerivAlong (I := I) g γ Vsec t) : TangentBundle I M)) (Set.Icc 0 L) :=
        sectionAlongCurve_continuousOn_totalSpace_of_contMDiffOn (I := I) γ
          (covDerivAlong (I := I) g γ Vsec) hγ_C1On (fun t _ => hnablaV_diff t)
      have hnablaVsq_cont : ContinuousOn
          (fun t : ℝ => g.inner (γ t) (covDerivAlong (I := I) g γ Vsec t)
            (covDerivAlong (I := I) g γ Vsec t)) (Set.Icc 0 L) :=
        continuousOn_g_inner_along_curve (I := I) (M := M) g hnablaV_total hnablaV_total
      have hRsec_total : ContinuousOn
          (fun t : ℝ => (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
            (γ t)
            ((DifferentialGeometry.Integral.Connection.riemannOp
              (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g) (γ t))
              (V t) (γ' t) (γ' t)) : TangentBundle I M)) (Set.Icc 0 L) :=
        ((((DifferentialGeometry.Integral.Connection.riemannOp_section_continuous
            (I := I) g).comp_continuousOn
            (s := Set.Icc (0 : ℝ) L) hγ_C1On.continuousOn).clm_bundle_apply
            hV_total).clm_bundle_apply hγ'_total).clm_bundle_apply hγ'_total
      have hRcurv_cont : ContinuousOn
          (fun t : ℝ => g.inner (γ t)
            ((DifferentialGeometry.Integral.Connection.riemannOp
              (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g) (γ t))
              (V t) (γ' t) (γ' t)) (V t)) (Set.Icc 0 L) :=
        continuousOn_g_inner_along_curve (I := I) (M := M) g hRsec_total hV_total
      have hindexFormIntegrand_continuousOn :
          ContinuousOn (fun t : ℝ => indexFormIntegrand (I := I) g γ V V t) (Set.Icc 0 L) := by
        have heq : (fun t : ℝ => indexFormIntegrand (I := I) g γ V V t)
            = (fun t : ℝ => g.inner (γ t) (covDerivAlong (I := I) g γ V t)
                (covDerivAlong (I := I) g γ V t)
              - g.inner (γ t)
                ((DifferentialGeometry.Integral.Connection.riemannOp
                  (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g) (γ t))
                  (V t) (γ' t) (γ' t)) (V t)) := rfl
        rw [heq]
        refine ContinuousOn.sub ?_ hRcurv_cont
        have hVfunsec : (V : ∀ t, TangentSpace I (γ t)) = Vsec := by
          funext s; exact (hVsec_eq s).symm
        rw [hVfunsec]
        exact hnablaVsq_cont
      have hg_ss_continuousOn : ContinuousOn g_ss (Set.Icc 0 L) := by
        have hC : ContDiff ℝ (5 : ℕ) (fun p : ℝ × ℝ =>
            fderiv ℝ (fun q : ℝ × ℝ => fderiv ℝ G q (1, 0)) p (1, 0)) := by
          have hfd1 : ContDiff ℝ (6 : ℕ) (fun p : ℝ × ℝ => fderiv ℝ G p) :=
            hGcdiff.fderiv_right (by exact_mod_cast (by norm_num : (6 : ℕ) + 1 ≤ 7))
          have hfd1app : ContDiff ℝ (6 : ℕ) (fun p : ℝ × ℝ => fderiv ℝ G p (1, 0)) :=
            (ContinuousLinearMap.apply ℝ ℝ ((1, 0) : ℝ × ℝ)).contDiff.comp hfd1
          have hfd2 : ContDiff ℝ (5 : ℕ) (fun p : ℝ × ℝ => fderiv ℝ
              (fun q : ℝ × ℝ => fderiv ℝ G q (1, 0)) p) :=
            hfd1app.fderiv_right (by exact_mod_cast (by norm_num : (5 : ℕ) + 1 ≤ 6))
          exact (ContinuousLinearMap.apply ℝ ℝ ((1, 0) : ℝ × ℝ)).contDiff.comp hfd2
        have hgsslice : ContinuousOn (fun t : ℝ =>
            fderiv ℝ (fun q : ℝ × ℝ => fderiv ℝ G q (1, 0)) (0, t) (1, 0)) (Set.Icc 0 L) := by
          have hincl : Continuous (fun t : ℝ => ((0 : ℝ), t)) :=
            continuous_const.prodMk continuous_id
          exact (hC.continuous.comp hincl).continuousOn
        exact hgsslice
      have hindexFormIntegrand_intervalIntegrable :
          IntervalIntegrable (fun t : ℝ => indexFormIntegrand (I := I) g γ V V t)
            MeasureTheory.volume 0 L := by
        apply ContinuousOn.intervalIntegrable
        rw [Set.uIcc_of_le (le_of_lt hL)]
        exact hindexFormIntegrand_continuousOn
      have hBsec_continuousOn :
          ContinuousOn (fun t : ℝ => g.inner (γ t) (Bsec t) (γ' t)) (Set.Icc 0 L) := by
        apply ContinuousOn.congr
          (f := fun t : ℝ => g_ss t / 2 - indexFormIntegrand (I := I) g γ V V t)
        · exact (hg_ss_continuousOn.div_const 2).sub hindexFormIntegrand_continuousOn
        · intro t ht
          have := hpt_id t ht
          linarith [this]
      have hBsec_intervalIntegrable :
          IntervalIntegrable (fun t : ℝ => g.inner (γ t) (Bsec t) (γ' t))
            MeasureTheory.volume 0 L := by
        apply ContinuousOn.intervalIntegrable
        rw [Set.uIcc_of_le (le_of_lt hL)]
        exact hBsec_continuousOn
      have hBint : (∫ t in (0 : ℝ)..L, g.inner (γ t) (Bsec t) (γ' t)) = 0 := by
        have hFTC : (∫ t in (0 : ℝ)..L, g.inner (γ t) (Bsec t) (γ' t))
            = g.inner (γ L) (Asec L) (γ' L) - g.inner (γ 0) (Asec 0) (γ' 0) := by
          apply intervalIntegral.integral_eq_sub_of_hasDerivAt
          · intro t ht
            rw [Set.uIcc_of_le (le_of_lt hL)] at ht
            exact hDderiv t ht
          · exact hBsec_intervalIntegrable
        rw [hFTC, hAsec0, hAsecL]
        simp
      have hsplit : (∫ t in (0 : ℝ)..L, g_ss t / 2)
          = (∫ t in (0 : ℝ)..L, indexFormIntegrand (I := I) g γ V V t)
            + (∫ t in (0 : ℝ)..L, g.inner (γ t) (Bsec t) (γ' t)) := by
        rw [← intervalIntegral.integral_add hindexFormIntegrand_intervalIntegrable hBsec_intervalIntegrable]
        refine intervalIntegral.integral_congr (fun t ht => ?_)
        rw [Set.uIcc_of_le (le_of_lt hL)] at ht
        exact hpt_id t ht
      rw [hsplit, hBint, add_zero, indexForm_eq_intervalIntegral]
    have hQint : (∫ t in (0 : ℝ)..L, Q (0, t)) = indexForm (I := I) g γ 0 L V V := by
      rw [← hgss_int]
      refine intervalIntegral.integral_congr (fun t ht => ?_)
      rw [Set.uIcc_of_le (le_of_lt hL)] at ht
      exact hQpt t ht
    rw [hQint] at hg₁_H1
    exact hg₁_H1
  have hmem : Set.Ioo (-δ) δ ∈ nhds (0 : ℝ) := Ioo_mem_nhds (by linarith) hδpos
  exact hg₁_deriv.congr_of_eventuallyEq
    (Filter.eventuallyEq_of_mem hmem (fun s hs => hderiv_eq s hs))

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 4000000 in

omit [NeZero (Module.finrank ℝ E)] in
theorem indexFormIntegrand_intervalIntegrable
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M) (L : ℝ) (_hL : 0 < L)
    (_hγ_C1 : ContMDiffOn (𝓘(ℝ, ℝ)) I 1 γ (Set.Icc 0 L))
    (_hγ_geoOn : IsGeodesicOn (I := I) g γ (Set.Icc 0 L))
    (_hγ_unit : ∀ t ∈ Set.Icc (0 : ℝ) L,
      g.inner (γ t)
          (mfderiv (𝓘(ℝ, ℝ)) I γ t (1 : ℝ))
          (mfderiv (𝓘(ℝ, ℝ)) I γ t (1 : ℝ)) = 1)
    (e : Fin (Module.finrank ℝ E - 1) → SectionAlongCurve I M γ)
    (_heDiff : ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) L,
      DifferentiableAt ℝ
        (DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong.chartRepAt
          (I := I) γ (e i).toFun t) t)
    (_hParallel : ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) L,
      DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong.covDerivAlong
        (I := I) g γ (e i).toFun t = 0)
    (_hON : ∀ t ∈ Set.Icc (0 : ℝ) L, ∀ i j,
      g.inner (γ t) ((e i).toFun t) ((e j).toFun t) = if i = j then 1 else 0)
    (_hPerp : ∀ t ∈ Set.Icc (0 : ℝ) L, ∀ i,
      g.inner (γ t) ((e i).toFun t) (mfderiv (𝓘(ℝ, ℝ)) I γ t (1 : ℝ)) = 0) :
    ∀ i : Fin (Module.finrank ℝ E - 1),
      IntervalIntegrable
        (fun t : ℝ => indexFormIntegrand (I := I) g γ
          ((SectionAlongCurve.smulFun
            (fun s => Real.sin (Real.pi * s / L)) (e i)).toFun)
          ((SectionAlongCurve.smulFun
            (fun s => Real.sin (Real.pi * s / L)) (e i)).toFun) t)
        MeasureTheory.volume 0 L := by
  intro i
  classical
  set c : ℝ → ℝ := fun s => Real.sin (Real.pi * s / L) with hc_def
  have hL_nn : (0 : ℝ) ≤ L := le_of_lt _hL
  have hc_contdiff : ContDiff ℝ ∞ c :=
    Real.contDiff_sin.comp ((contDiff_const.mul contDiff_id).div_const _)
  have hc_cont : Continuous c := hc_contdiff.continuous
  have hderiv_c_cont : Continuous (deriv c) := hc_contdiff.continuous_deriv (by simp)
  have hc_diff : ∀ t, DifferentiableAt ℝ c t :=
    fun t => hc_contdiff.differentiable (by simp) t
  have he_total : ContinuousOn
      (fun t : ℝ => (TotalSpace.mk' E (γ t) ((e i).toFun t) : TangentBundle I M))
      (Set.Icc 0 L) :=
    DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong.sectionAlongCurve_continuousOn_totalSpace_of_contMDiffOn
      (I := I) γ (e i).toFun _hγ_C1 (fun t ht => _heDiff i t ht)
  have hA : ContinuousOn (fun t : ℝ => g.inner (γ t) ((e i).toFun t) ((e i).toFun t))
      (Set.Icc 0 L) :=
    continuousOn_g_inner_along_curve (I := I) (M := M) g he_total he_total
  have hUnique : UniqueMDiffOn 𝓘(ℝ, ℝ) (Set.Icc (0 : ℝ) L) := by
    intro u hu
    rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
    exact (uniqueDiffOn_Icc _hL) u hu
  have hTan := _hγ_C1.continuousOn_tangentMapWithin (le_refl 1) hUnique
  have hLift : Continuous (fun u : ℝ =>
      (⟨u, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) := by
    have h_homeo :
        Continuous ((tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ)).symm :
          ModelProd ℝ ℝ → TangentBundle 𝓘(ℝ, ℝ) ℝ) :=
      (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ)).symm.continuous
    exact h_homeo.comp (continuous_id.prodMk continuous_const)
  have hMaps : Set.MapsTo
      (fun u : ℝ => (⟨u, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ))
      (Set.Icc (0 : ℝ) L) (Bundle.TotalSpace.proj ⁻¹' (Set.Icc (0 : ℝ) L)) := by
    intro u hu
    simpa using hu
  have hVW : ContinuousOn
      (fun t : ℝ =>
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (γ t)
          (mfderivWithin 𝓘(ℝ, ℝ) I γ (Set.Icc (0 : ℝ) L) t (1 : ℝ)) :
            TangentBundle I M))
      (Set.Icc (0 : ℝ) L) := by
    have hComp : ContinuousOn
        (fun t : ℝ => tangentMapWithin 𝓘(ℝ, ℝ) I γ (Set.Icc (0 : ℝ) L)
          (⟨t, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ))
        (Set.Icc (0 : ℝ) L) :=
      hTan.comp hLift.continuousOn hMaps
    exact hComp.congr (fun t _ => rfl)
  have hR3 : ContinuousOn
      (fun t : ℝ => (TotalSpace.mk' E
        (E := (TangentSpace I : M → Type _))
        (γ t)
        (DifferentialGeometry.Integral.Connection.riemannOp
          (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g) (γ t)
          ((e i).toFun t)
          (mfderivWithin 𝓘(ℝ, ℝ) I γ (Set.Icc (0 : ℝ) L) t (1 : ℝ))
          (mfderivWithin 𝓘(ℝ, ℝ) I γ (Set.Icc (0 : ℝ) L) t (1 : ℝ)))))
      (Set.Icc 0 L) :=
    ((((DifferentialGeometry.Integral.Connection.riemannOp_section_continuous
        (I := I) g).comp_continuousOn
        (s := Set.Icc (0 : ℝ) L) _hγ_C1.continuousOn).clm_bundle_apply
        he_total).clm_bundle_apply hVW).clm_bundle_apply hVW
  have hB : ContinuousOn
      (fun t : ℝ => g.inner (γ t)
        (DifferentialGeometry.Integral.Connection.riemannOp
          (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g) (γ t)
          ((e i).toFun t)
          (mfderivWithin 𝓘(ℝ, ℝ) I γ (Set.Icc (0 : ℝ) L) t (1 : ℝ))
          (mfderivWithin 𝓘(ℝ, ℝ) I γ (Set.Icc (0 : ℝ) L) t (1 : ℝ)))
        ((e i).toFun t))
      (Set.Icc 0 L) :=
    continuousOn_g_inner_along_curve (I := I) (M := M) g hR3 he_total
  have hIntW : IntervalIntegrable
      (fun t : ℝ =>
        (deriv c t * deriv c t) * g.inner (γ t) ((e i).toFun t) ((e i).toFun t)
        - (c t * c t) * g.inner (γ t)
            (DifferentialGeometry.Integral.Connection.riemannOp
              (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g) (γ t)
              ((e i).toFun t)
              (mfderivWithin 𝓘(ℝ, ℝ) I γ (Set.Icc (0 : ℝ) L) t (1 : ℝ))
              (mfderivWithin 𝓘(ℝ, ℝ) I γ (Set.Icc (0 : ℝ) L) t (1 : ℝ)))
            ((e i).toFun t))
      MeasureTheory.volume 0 L := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hL_nn]
    refine ContinuousOn.sub ?_ ?_
    · exact ((hderiv_c_cont.mul hderiv_c_cont).continuousOn).mul hA
    · exact ((hc_cont.mul hc_cont).continuousOn).mul hB
  refine hIntW.congr_ae ?_
  have hIoo_ae : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) L)),
      t ∈ Set.Ioo (0 : ℝ) L := by
    rw [Set.uIoc_of_le hL_nn, ← MeasureTheory.restrict_Ioo_eq_restrict_Ioc]
    exact MeasureTheory.ae_restrict_mem measurableSet_Ioo
  filter_upwards [hIoo_ae] with t ht
  have htIcc : t ∈ Set.Icc (0 : ℝ) L := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
  have hmem : Set.Icc (0 : ℝ) L ∈ nhds t := Icc_mem_nhds ht.1 ht.2
  change (deriv c t * deriv c t) * g.inner (γ t) ((e i).toFun t) ((e i).toFun t)
      - (c t * c t) * g.inner (γ t)
          (DifferentialGeometry.Integral.Connection.riemannOp
            (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g) (γ t)
            ((e i).toFun t)
            (mfderivWithin 𝓘(ℝ, ℝ) I γ (Set.Icc (0 : ℝ) L) t (1 : ℝ))
            (mfderivWithin 𝓘(ℝ, ℝ) I γ (Set.Icc (0 : ℝ) L) t (1 : ℝ)))
          ((e i).toFun t)
    = indexFormIntegrand (I := I) g γ
        ((SectionAlongCurve.smulFun c (e i)).toFun)
        ((SectionAlongCurve.smulFun c (e i)).toFun) t
  rw [mfderivWithin_of_mem_nhds hmem]
  have hnabla :
      DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong.covDerivAlong
        (I := I) g γ (SectionAlongCurve.smulFun c (e i)).toFun t
        = deriv c t • (e i).toFun t := by
    have key :=
      DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong.covDerivAlong_smulFun
        (I := I) g γ c (e i).toFun t (hc_diff t) (_heDiff i t htIcc)
    rw [_hParallel i t htIcc, smul_zero, add_zero] at key
    exact key
  have hfac1 : g.inner (γ t) (deriv c t • (e i).toFun t) (deriv c t • (e i).toFun t)
      = (deriv c t * deriv c t) * g.inner (γ t) ((e i).toFun t) ((e i).toFun t) := by
    have key : ∀ (x : TangentSpace I (γ t)) (a : ℝ),
        g.inner (γ t) (a • x) (a • x) = (a * a) * g.inner (γ t) x x := by
      intro x a
      simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
      ring
    exact key ((e i).toFun t) (deriv c t)
  have hfac2 : g.inner (γ t)
      (DifferentialGeometry.Integral.Connection.riemannOp
        (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g) (γ t)
        (c t • (e i).toFun t)
        (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)) (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)))
      (c t • (e i).toFun t)
      = (c t * c t) * g.inner (γ t)
          (DifferentialGeometry.Integral.Connection.riemannOp
            (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g) (γ t)
            ((e i).toFun t)
            (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)) (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)))
          ((e i).toFun t) := by
    have key : ∀ (x w : TangentSpace I (γ t)) (a : ℝ),
        g.inner (γ t)
          (DifferentialGeometry.Integral.Connection.riemannOp
            (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g) (γ t)
            (a • x) w w) (a • x)
          = (a * a) * g.inner (γ t)
              (DifferentialGeometry.Integral.Connection.riemannOp
                (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g) (γ t)
                x w w) x := by
      intro x w a
      simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
      ring
    exact key ((e i).toFun t) (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)) (c t)
  unfold indexFormIntegrand
  simp only [SectionAlongCurve.smulFun_toFun]
  rw [hnabla, hfac1, hfac2]

end Variation
end Riemannian
end Geometry
end DifferentialGeometry

end
