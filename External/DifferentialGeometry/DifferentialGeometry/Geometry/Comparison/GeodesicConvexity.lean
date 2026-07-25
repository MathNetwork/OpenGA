import DifferentialGeometry.Geometry.Exponential.GaussLemma
import DifferentialGeometry.Geometry.Exponential.IntrinsicExp
import DifferentialGeometry.Geometry.Exponential.IntrinsicExpContinuity
import DifferentialGeometry.Geometry.Exponential.MinimizingGeodesic
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.UnitInterval



open Set Bundle Manifold
open scoped Topology Manifold ContDiff ENNReal

noncomputable section

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian

def IsGeodesicallyConvexWith {M : Type*} [TopologicalSpace M]
    (join : M → M → ℝ → M) (S : Set M) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S,
    ContinuousOn (join a b) unitInterval ∧ join a b 0 = a ∧ join a b 1 = b ∧
      (∀ t ∈ unitInterval, join a b t ∈ S)

namespace IsGeodesicallyConvexWith

variable {M : Type*} [TopologicalSpace M] {join : M → M → ℝ → M} {S T : Set M}

theorem joinedIn (hS : IsGeodesicallyConvexWith join S) {a b : M}
    (ha : a ∈ S) (hb : b ∈ S) : JoinedIn S a b := by
  obtain ⟨hcont, h0, h1, hmem⟩ := hS a ha b hb
  refine JoinedIn.ofLine hcont h0 h1 ?_
  rintro x ⟨t, ht, rfl⟩
  exact hmem t ht

theorem inter (hS : IsGeodesicallyConvexWith join S)
    (hT : IsGeodesicallyConvexWith join T) :
    IsGeodesicallyConvexWith join (S ∩ T) := by
  rintro a ⟨haS, haT⟩ b ⟨hbS, hbT⟩
  obtain ⟨hcontS, h0, h1, hmemS⟩ := hS a haS b hbS
  obtain ⟨_, _, _, hmemT⟩ := hT a haT b hbT
  exact ⟨hcontS, h0, h1, fun t ht => ⟨hmemS t ht, hmemT t ht⟩⟩

theorem joinedIn_inter (hS : IsGeodesicallyConvexWith join S)
    (hT : IsGeodesicallyConvexWith join T) {a b : M}
    (haS : a ∈ S) (haT : a ∈ T) (hbS : b ∈ S) (hbT : b ∈ T) :
    JoinedIn (S ∩ T) a b :=
  (hS.inter hT).joinedIn ⟨haS, haT⟩ ⟨hbS, hbT⟩

end IsGeodesicallyConvexWith

section IntrinsicBall

open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Integral.Measure

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
variable [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]

def smallNormalBall (p : M) (ρ : ℝ) : Set M :=
  {q : M | riemannianEDist I p q < ENNReal.ofReal ρ}

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M] in
@[simp] lemma mem_smallNormalBall {p q : M} {ρ : ℝ} :
    q ∈ smallNormalBall (I := I) p ρ ↔ riemannianEDist I p q < ENNReal.ofReal ρ :=
  Iff.rfl

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M] in
lemma centre_mem_smallNormalBall (p : M) {ρ : ℝ} (hρ : 0 < ρ) :
    p ∈ smallNormalBall (I := I) p ρ := by
  rw [mem_smallNormalBall, riemannianEDist_self]
  exact ENNReal.ofReal_pos.2 hρ

variable [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [T2Space (TangentBundle I M)]
  [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]

noncomputable def minimizingVec
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (a b : M) : TangentSpace I a :=
  Classical.choose
    (hopf_rinow_expMapIntrinsic_surjective_minimizing
      (I := I) g hEnorm a b)


theorem minimizingVec_exp
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (a b : M) :
    expMapIntrinsic (I := I) g hEnorm a (minimizingVec (I := I) g hEnorm a b) = b :=
  (Classical.choose_spec
    (hopf_rinow_expMapIntrinsic_surjective_minimizing
      (I := I) g hEnorm a b)).1


theorem minimizingVec_len
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (a b : M) :
    Real.sqrt (g.inner a (minimizingVec (I := I) g hEnorm a b)
        (minimizingVec (I := I) g hEnorm a b)) =
      (riemannianEDist I a b).toReal :=
  (Classical.choose_spec
    (hopf_rinow_expMapIntrinsic_surjective_minimizing
      (I := I) g hEnorm a b)).2


noncomputable def minJoin
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (a b : M) (t : ℝ) : M :=
  intrinsicGeodesic (I := I) g hEnorm a
    (minimizingVec (I := I) g hEnorm a b) t


@[simp] theorem minJoin_zero
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (a b : M) : minJoin (I := I) g hEnorm a b 0 = a := by
  exact intrinsicGeodesic_zero (I := I) g hEnorm a
    (minimizingVec (I := I) g hEnorm a b)


@[simp] theorem minJoin_one
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (a b : M) : minJoin (I := I) g hEnorm a b 1 = b := by
  change intrinsicGeodesic (I := I) g hEnorm a
    (minimizingVec (I := I) g hEnorm a b) 1 = b
  rw [← expMapIntrinsic_def, minimizingVec_exp]


theorem minJoin_cont
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (a b : M) : Continuous (minJoin (I := I) g hEnorm a b) :=
  intrinsicGeodesic_continuous (I := I) g hEnorm a
    (minimizingVec (I := I) g hEnorm a b)


theorem minJoin_edist_le
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (a b : M) {t : ℝ} (ht : 0 ≤ t) :
    riemannianEDist I a (minJoin (I := I) g hEnorm a b t) ≤
      ENNReal.ofReal ((riemannianEDist I a b).toReal * t) := by
  simpa only [minJoin, intrinsicGeodesic_zero, minimizingVec_len, sub_zero] using
    intrinsicGeodesic_riemannianEDist_le
      (I := I) g hEnorm a (minimizingVec (I := I) g hEnorm a b)
        (s := 0) (t := t) ht

omit [T2Space (TangentBundle I M)] in
omit [ConnectedSpace M] in
private lemma intrinsicGeodesic_speedSq_const
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (v : TangentSpace I p) (t : ℝ) :
    g.inner (intrinsicGeodesic (I := I) g hEnorm p v t)
        (mfderiv 𝓘(ℝ, ℝ) I (intrinsicGeodesic (I := I) g hEnorm p v) t 1)
        (mfderiv 𝓘(ℝ, ℝ) I (intrinsicGeodesic (I := I) g hEnorm p v) t 1)
      = g.inner p v v := by
  set γ : ℝ → M := intrinsicGeodesic (I := I) g hEnorm p v with hγ_def
  have hgeo : IsGeodesic (I := I) g γ :=
    intrinsicGeodesic_isGeodesic (I := I) g hEnorm p v
  have hC1 : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ Set.univ :=
    intrinsicGeodesic_contMDiffOn (I := I) g hEnorm p v
  have hconst := HopfRinow.isGeodesicOn_speedSq_const (I := I) g (t₀ := t) (t₁ := 0)
    isOpen_univ (hgeo.isGeodesicOn Set.univ) hC1 (Set.subset_univ _)
  rw [hconst]
  have h0 : γ 0 = p := intrinsicGeodesic_zero (I := I) g hEnorm p v
  have hvelE : (mfderiv 𝓘(ℝ, ℝ) I γ 0 (1 : ℝ) : E) = (v : E) :=
    intrinsicGeodesic_mfderiv_zero (I := I) g hEnorm p v
  exact congrArg₂ (fun (x : M) (w : E) => g.inner x w w) h0 hvelE

omit [T2Space (TangentBundle I M)] in
omit [ConnectedSpace M] in
private lemma intrinsicGeodesic_velocity_enorm_le'
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (v : TangentSpace I p) (t : ℝ) :
    ‖mfderiv 𝓘(ℝ, ℝ) I (intrinsicGeodesic (I := I) g hEnorm p v) t (1 : ℝ)‖ₑ
      ≤ ENNReal.ofReal (Real.sqrt (g.inner p v v)) := by
  set γ : ℝ → M := intrinsicGeodesic (I := I) g hEnorm p v with hγ_def
  have hnn : (0 : ℝ) ≤ g.inner p v v := by
    rcases eq_or_ne v 0 with h | h
    · subst h; simp
    · exact (g.pos p v h).le
  set c : ℝ := Real.sqrt (g.inner p v v) with hc_def
  have hc_nn : (0 : ℝ) ≤ c := Real.sqrt_nonneg _
  have hspeedSq : g.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t 1)
      (mfderiv 𝓘(ℝ, ℝ) I γ t 1) = c ^ 2 := by
    rw [intrinsicGeodesic_speedSq_const (I := I) g hEnorm p v t, hc_def,
      Real.sq_sqrt hnn]
  rw [hEnorm]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  calc Real.sqrt (g.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t 1) (mfderiv 𝓘(ℝ, ℝ) I γ t 1))
      = Real.sqrt (c ^ 2) := by rw [hspeedSq]
    _ = c := Real.sqrt_sq hc_nn

omit [T2Space (TangentBundle I M)] in
omit [ConnectedSpace M] in
theorem intrinsicGeodesic_riemannianEDist_le_radius
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (v : TangentSpace I p) {t : ℝ} (ht : 0 ≤ t) :
    riemannianEDist I p (intrinsicGeodesic (I := I) g hEnorm p v t)
      ≤ ENNReal.ofReal (Real.sqrt (g.inner p v v) * t) := by
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  set γ : ℝ → M := intrinsicGeodesic (I := I) g hEnorm p v with hγ_def
  set c : ℝ := Real.sqrt (g.inner p v v) with hc_def
  have hc_nn : (0 : ℝ) ≤ c := Real.sqrt_nonneg _
  have hγ0 : γ 0 = p := intrinsicGeodesic_zero (I := I) g hEnorm p v
  have hγ_C1 : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Set.Icc 0 t) :=
    (intrinsicGeodesic_contMDiffOn (I := I) g hEnorm p v).mono (Set.subset_univ _)
  have h_pathLen_le : pathELength I γ 0 t ≤ ENNReal.ofReal (c * t) := by
    rw [Manifold.pathELength_eq_lintegral_mfderiv_Icc]
    have h_le :
        ∫⁻ τ in Set.Icc 0 t, (fun τ => ‖mfderiv 𝓘(ℝ, ℝ) I γ τ (1 : ℝ)‖ₑ) τ
          ≤ ∫⁻ _ in Set.Icc 0 t, ENNReal.ofReal c := by
      refine MeasureTheory.setLIntegral_mono' measurableSet_Icc (fun τ _ => ?_)
      simpa [hγ_def, hc_def] using
        intrinsicGeodesic_velocity_enorm_le' (I := I) g hEnorm p v τ
    have h_const :
        (∫⁻ _ in Set.Icc 0 t, ENNReal.ofReal c)
          = ENNReal.ofReal c * MeasureTheory.volume (Set.Icc 0 t) :=
      MeasureTheory.setLIntegral_const (Set.Icc 0 t) (ENNReal.ofReal c)
    have h_vol : MeasureTheory.volume (Set.Icc 0 t) = ENNReal.ofReal (t - 0) :=
      Real.volume_Icc
    calc
      ∫⁻ τ in Set.Icc 0 t, ‖mfderiv 𝓘(ℝ, ℝ) I γ τ (1 : ℝ)‖ₑ
          ≤ ∫⁻ _ in Set.Icc 0 t, ENNReal.ofReal c := h_le
      _ = ENNReal.ofReal c * MeasureTheory.volume (Set.Icc 0 t) := h_const
      _ = ENNReal.ofReal c * ENNReal.ofReal (t - 0) := by rw [h_vol]
      _ = ENNReal.ofReal (c * (t - 0)) := (ENNReal.ofReal_mul hc_nn).symm
      _ = ENNReal.ofReal (c * t) := by ring_nf
  have h_dist_le : riemannianEDist I (γ 0) (γ t) ≤ pathELength I γ 0 t :=
    riemannianEDist_le_pathELength (I := I) (γ := γ) (a := 0) (b := t)
      hγ_C1 rfl rfl ht
  calc riemannianEDist I p (γ t)
      = riemannianEDist I (γ 0) (γ t) := by rw [hγ0]
    _ ≤ pathELength I γ 0 t := h_dist_le
    _ ≤ ENNReal.ofReal (c * t) := h_pathLen_le

omit [T2Space (TangentBundle I M)] in
omit [ConnectedSpace M] in
theorem smallNormalBall_radial_confined
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (v : TangentSpace I p) {ρ : ℝ}
    (hv : Real.sqrt (g.inner p v v) < ρ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    intrinsicGeodesic (I := I) g hEnorm p v t ∈ smallNormalBall (I := I) p ρ := by
  obtain ⟨ht0, ht1⟩ := ht
  set c : ℝ := Real.sqrt (g.inner p v v) with hc_def
  have hc_nn : (0 : ℝ) ≤ c := Real.sqrt_nonneg _
  have hbound := intrinsicGeodesic_riemannianEDist_le_radius (I := I) g hEnorm p v ht0
  rw [mem_smallNormalBall]
  refine lt_of_le_of_lt hbound ?_
  refine lt_of_le_of_lt (ENNReal.ofReal_le_ofReal ?_) (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hc_nn |>.2 hv)
  calc c * t ≤ c * 1 := by
        exact mul_le_mul_of_nonneg_left ht1 hc_nn
    _ = c := mul_one c

omit [T2Space (TangentBundle I M)] in
omit [ConnectedSpace M] in
theorem joinedIn_centre_smallNormalBall
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (v : TangentSpace I p) {ρ : ℝ}
    (hv : Real.sqrt (g.inner p v v) < ρ) :
    JoinedIn (smallNormalBall (I := I) p ρ) p
      (expMapIntrinsic (I := I) g hEnorm p v) := by
  set γ : ℝ → M := intrinsicGeodesic (I := I) g hEnorm p v with hγ_def
  have hγ_cont : Continuous γ := intrinsicGeodesic_continuous (I := I) g hEnorm p v
  have hγ0 : γ 0 = p := intrinsicGeodesic_zero (I := I) g hEnorm p v
  have hγ1 : γ 1 = expMapIntrinsic (I := I) g hEnorm p v := rfl
  refine JoinedIn.ofLine hγ_cont.continuousOn hγ0 hγ1 ?_
  rintro x ⟨t, ht, rfl⟩
  exact smallNormalBall_radial_confined (I := I) g hEnorm p v hv ht

end IntrinsicBall

end Riemannian
end Geometry
end DifferentialGeometry

end
