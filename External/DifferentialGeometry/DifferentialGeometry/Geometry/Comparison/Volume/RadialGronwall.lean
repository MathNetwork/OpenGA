import DifferentialGeometry.Geometry.Comparison.Variation.CovariantGronwall
import DifferentialGeometry.Geometry.Comparison.Variation.PerpFrame
import DifferentialGeometry.Geometry.Comparison.Volume.NormalChartMeasure
import DifferentialGeometry.Geometry.Curvature.MetricLeviCivitaReconcile
import DifferentialGeometry.Geometry.Curvature.RicciOperatorNormBound
import DifferentialGeometry.Geometry.Exponential.GaussLemmaPullback
import DifferentialGeometry.Tensor.RSTensor.CotangentRiemannian










noncomputable section

open Set
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace VolumeComparison

open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

section Radial

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
  [T2Space (TangentBundle I M)]


def radialCurve (g : SmoothRiemannianMetric I M) (p : M) (x : E) (t : ℝ) : M :=
  expMap (I := I) g p (show TangentSpace I p from (t • x))

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
@[simp] lemma radialCurve_apply
    (g : SmoothRiemannianMetric I M) (p : M) (x : E) (t : ℝ) :
    radialCurve (I := I) g p x t =
      expMap (I := I) g p (show TangentSpace I p from (t • x)) :=
  rfl

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
@[simp] lemma radialCurve_one
    (g : SmoothRiemannianMetric I M) (p : M) (x : E) :
    radialCurve (I := I) g p x 1 =
      expMap (I := I) g p (show TangentSpace I p from x) := by
  simp [radialCurve]

omit [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma radialCurve_zero
    (g : SmoothRiemannianMetric I M) (p : M) (x : E) :
    radialCurve (I := I) g p x 0 = p := by
  unfold radialCurve
  rw [zero_smul]
  exact expMap_zero (I := I) g p



omit [T2Space M] in
omit [SigmaCompactSpace M] in
theorem exists_radialJacobi_diff
    (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ r : ℝ, 0 < r ∧ ∀ x w : E, ‖x‖ < r → ‖w‖ < r → ∀ {b : ℝ}, b ≤ 1 →
      (∀ t ∈ Icc (0 : ℝ) b,
        DifferentiableAt ℝ
          (chartRepAt (I := I) (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) t) t) ∧
      (∀ t ∈ Icc (0 : ℝ) b,
        DifferentiableAt ℝ
          (chartRepAt (I := I) (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) s) t) t) := by
  simpa [radialCurve, radialJacobiField] using
    DifferentialGeometry.Geometry.Riemannian.exists_jacobi_diff (I := I) g p



omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
theorem radial_mem_expBall
    (g : SmoothRiemannianMetric I M) (p : M) (x : E)
    {ρ b : Real} (hxρ : ‖x‖ < ρ) (hb : b ≤ 1) :
    ∀ t : Real, t ∈ Ioo (0 : Real) b →
      radialCurve (I := I) g p x t ∈
        (fun v : TangentSpace I p => expMap (I := I) g p v) ''
          {v : TangentSpace I p | ‖v‖ < ρ} := by
  intro t ht
  refine ⟨(show TangentSpace I p from t • x), ?_, ?_⟩
  · have ht_nonneg : 0 ≤ t := le_of_lt ht.1
    have ht_le_one : t ≤ 1 := le_trans (le_of_lt ht.2) hb
    calc
      ‖(show TangentSpace I p from t • x)‖ = ‖t • x‖ := rfl
      _ = ‖t‖ * ‖x‖ := norm_smul t x
      _ = t * ‖x‖ := by rw [Real.norm_of_nonneg ht_nonneg]
      _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right ht_le_one (norm_nonneg x)
      _ = ‖x‖ := one_mul ‖x‖
      _ < ρ := hxρ
  · rfl



omit [T2Space M] [SigmaCompactSpace M] in
omit [T2Space (TangentBundle I M)] in
lemma exists_radialFrame
    (g : SmoothRiemannianMetric I M) (p : M) (x : E)
    {b : ℝ} (hb : 0 < b)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) (radialCurve (I := I) g p x)) :
    ∃ F : Fin (Module.finrank ℝ (TangentSpace I (radialCurve (I := I) g p x 0))) →
        ∀ t : ℝ, TangentSpace I (radialCurve (I := I) g p x t),
      (∀ t ∈ Icc (0 : ℝ) b,
        Fintype.card (Fin (Module.finrank ℝ (TangentSpace I (radialCurve (I := I) g p x 0)))) =
          Module.finrank ℝ (TangentSpace I (radialCurve (I := I) g p x t))) ∧
      (∀ i, ∀ t ∈ Icc (0 : ℝ) b,
        DifferentiableAt ℝ (chartRepAt (I := I) (radialCurve (I := I) g p x) (F i) t) t) ∧
      (∀ i, ∀ t ∈ Icc (0 : ℝ) b,
        covDerivAlong (I := I) g (radialCurve (I := I) g p x) (F i) t = 0) ∧
      (∀ t ∈ Icc (0 : ℝ) b, ∀ i j,
        g.inner (radialCurve (I := I) g p x t) (F i t) (F j t) =
          if i = j then (1 : ℝ) else 0) := by
  classical
  obtain ⟨basis, hON0⟩ :=
    DifferentialGeometry.Integral.Connection.exists_gOrthonormalBasis
      (I := I) g (radialCurve (I := I) g p x 0)
  obtain ⟨F, _hF0, hFdiff, hFpar, hFON⟩ :=
    DifferentialGeometry.Geometry.Riemannian.exists_parallel_frame
      (I := I) g (radialCurve (I := I) g p x)
      (N := 2) (by norm_num) hγ hb basis hON0
  refine ⟨F, ?_, hFdiff, hFpar, hFON⟩
  intro t ht
  simp only [Fintype.card_fin]
  rfl



omit [T2Space M] [SigmaCompactSpace M] in
lemma radialCurve_contMDiffAt_Icc
    (g : SmoothRiemannianMetric I M) (p : M) (x : E) {b : ℝ}
    (hb : b ≤ 1)
    (hx : ‖x‖ < expMapC2Radius (I := I) g p) :
    ∀ t ∈ Icc (0 : ℝ) b,
      ContMDiffAt 𝓘(ℝ, ℝ) I (2 : ℕ∞)
        (radialCurve (I := I) g p x) t := by
  intro t ht
  have hnorm : ‖t • x‖ < expMapC2Radius (I := I) g p := by
    rw [norm_smul, Real.norm_eq_abs]
    have h0 : 0 ≤ t := ht.1
    have h1 : t ≤ 1 := le_trans ht.2 hb
    have habs : |t| ≤ 1 := by
      rw [abs_of_nonneg h0]
      exact h1
    calc
      |t| * ‖x‖ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right habs (norm_nonneg _)
      _ = ‖x‖ := one_mul _
      _ < expMapC2Radius (I := I) g p := hx
  simpa [radialCurve] using
    (DifferentialGeometry.Geometry.Riemannian.radialCurve_contMDiffAt2
      (I := I) g p x t hnorm)



omit [T2Space M] [SigmaCompactSpace M] in
lemma radialCurve_contMDiffOn_Icc
    (g : SmoothRiemannianMetric I M) (p : M) (x : E)
    (hx : ‖x‖ < expMapC2Radius (I := I) g p) :
    ContMDiffOn 𝓘(ℝ, ℝ) I (2 : ℕ∞)
      (radialCurve (I := I) g p x) (Icc (0 : ℝ) 1) := by
  intro t ht
  have hnorm : ‖t • x‖ < expMapC2Radius (I := I) g p := by
    rw [norm_smul, Real.norm_eq_abs]
    have h0 : 0 ≤ t := ht.1
    have h1 : t ≤ 1 := ht.2
    have habs : |t| ≤ 1 := by
      rw [abs_of_nonneg h0]
      exact h1
    calc
      |t| * ‖x‖ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right habs (norm_nonneg _)
      _ = ‖x‖ := one_mul _
      _ < expMapC2Radius (I := I) g p := hx
  simpa [radialCurve] using
    (DifferentialGeometry.Geometry.Riemannian.radialCurve_contMDiffAt2
      (I := I) g p x t hnorm).contMDiffWithinAt


omit [T2Space M] [SigmaCompactSpace M] in
lemma radialC2OnBallIcc
    (g : SmoothRiemannianMetric I M) (p : M) {R b : ℝ}
    (hR : R ≤ expMapC2Radius (I := I) g p) (hb : b ≤ 1) :
    ∀ w ∈ Metric.ball (0 : E) R,
      ContMDiffOn 𝓘(ℝ, ℝ) I (2 : ℕ∞)
        (radialCurve (I := I) g p w) (Icc (0 : ℝ) b) := by
  intro w hw
  have hwR : ‖w‖ < R := by
    simpa [Metric.mem_ball, dist_eq_norm] using hw
  exact (radialCurve_contMDiffOn_Icc (I := I) g p w (hwR.trans_le hR)).mono
    (by
      intro t ht
      exact ⟨ht.1, le_trans ht.2 hb⟩)




omit [T2Space M] [SigmaCompactSpace M] in
lemma exists_radial_clip
    (g : SmoothRiemannianMetric I M) (p : M) (x : E) {b : ℝ}
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hx : ‖x‖ < expMapC2Radius (I := I) g p) :
    ∃ tau : ℝ → ℝ, ContDiff ℝ (∞ : WithTop ℕ∞) tau ∧
      Set.EqOn tau id (Set.Icc 0 b) ∧
      ∀ t : ℝ, ‖tau t • x‖ < expMapC2Radius (I := I) g p := by
  classical
  let R := expMapC2Radius (I := I) g p
  have hRpos : 0 < R := DifferentialGeometry.Geometry.Riemannian.expMapC2Radius_pos
    (I := I) g p
  by_cases hxzero : ‖x‖ = 0
  · set lam : ℝ := b + 1 with hlam_def
    have hblam : b < lam := by rw [hlam_def]; linarith
    obtain ⟨tau, htau_cd, htau_eq, htau_bound⟩ :=
      DifferentialGeometry.Geometry.Riemannian.exists_time_clip
        (L := b) (lam := lam) hb0 hblam
    refine ⟨tau, htau_cd, htau_eq, ?_⟩
    intro t
    rw [norm_smul, hxzero, mul_zero]
    exact hRpos
  · have hxpos : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg x) (Ne.symm hxzero)
    have hratio : 1 < R / ‖x‖ := by
      rw [one_lt_div hxpos]
      simpa [R] using hx
    set lam : ℝ := (1 + R / ‖x‖) / 2 with hlam_def
    have h1lam : 1 < lam := by rw [hlam_def]; linarith
    have hblam : b < lam := lt_of_le_of_lt hb1 h1lam
    have hprod : lam * ‖x‖ < R := by
      have hprod_eq : lam * ‖x‖ = (‖x‖ + R) / 2 := by
        rw [hlam_def]
        field_simp [hxpos.ne']
      rw [hprod_eq]
      linarith [show ‖x‖ < R by simpa [R] using hx]
    obtain ⟨tau, htau_cd, htau_eq, htau_bound⟩ :=
      DifferentialGeometry.Geometry.Riemannian.exists_time_clip
        (L := b) (lam := lam) hb0 hblam
    refine ⟨tau, htau_cd, htau_eq, ?_⟩
    intro t
    rw [norm_smul, Real.norm_eq_abs]
    exact lt_of_le_of_lt
      (mul_le_mul_of_nonneg_right (htau_bound t) (norm_nonneg x)) hprod




omit [T2Space M] [SigmaCompactSpace M] in
lemma exists_rclip_nbhd
    (g : SmoothRiemannianMetric I M) (p : M) (x : E) {b : ℝ}
    (hb1 : b ≤ 1)
    (hx : ‖x‖ < expMapC2Radius (I := I) g p) :
    ∃ eps : ℝ, 0 < eps ∧ ∃ tau : ℝ → ℝ,
      ContDiff ℝ (∞ : WithTop ℕ∞) tau ∧
      Set.EqOn tau id (Set.Icc (-eps) (b + eps)) ∧
      ∀ t : ℝ, ‖tau t • x‖ < expMapC2Radius (I := I) g p := by
  classical
  let R := expMapC2Radius (I := I) g p
  have hRpos : 0 < R := DifferentialGeometry.Geometry.Riemannian.expMapC2Radius_pos
    (I := I) g p
  by_cases hxzero : ‖x‖ = 0
  · set lam : ℝ := 2 with hlam_def
    set eps : ℝ := (1 / 2 : ℝ) with heps_def
    have heps_pos : 0 < eps := by rw [heps_def]; norm_num
    have hlam_pos : 0 < lam := by rw [hlam_def]; norm_num
    obtain ⟨tau, htau_cd, htau_eq, htau_bound⟩ :=
      DifferentialGeometry.Geometry.Riemannian.exists_time_window_clip
        (a := -eps) (b := b + eps) (lam := lam) hlam_pos
        (by rw [hlam_def, heps_def]; norm_num)
        (by rw [hlam_def, heps_def]; linarith)
    refine ⟨eps, heps_pos, tau, htau_cd, htau_eq, ?_⟩
    intro t
    rw [norm_smul, hxzero, mul_zero]
    exact hRpos
  · have hxpos : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg x) (Ne.symm hxzero)
    have hratio : 1 < R / ‖x‖ := by
      rw [one_lt_div hxpos]
      simpa [R] using hx
    set lam : ℝ := (1 + R / ‖x‖) / 2 with hlam_def
    set eps : ℝ := (lam - 1) / 2 with heps_def
    have h1lam : 1 < lam := by rw [hlam_def]; linarith
    have hlam_pos : 0 < lam := by linarith
    have heps_pos : 0 < eps := by rw [heps_def]; linarith
    have heps_lt_lam : eps < lam := by rw [heps_def]; linarith
    have hb_eps_lt : b + eps < lam := by
      have hmid : 1 + eps < lam := by rw [heps_def]; linarith
      have hble : b + eps ≤ 1 + eps := by linarith
      exact lt_of_le_of_lt hble hmid
    have hprod : lam * ‖x‖ < R := by
      have hprod_eq : lam * ‖x‖ = (‖x‖ + R) / 2 := by
        rw [hlam_def]
        field_simp [hxpos.ne']
      rw [hprod_eq]
      linarith [show ‖x‖ < R by simpa [R] using hx]
    obtain ⟨tau, htau_cd, htau_eq, htau_bound⟩ :=
      DifferentialGeometry.Geometry.Riemannian.exists_time_window_clip
        (a := -eps) (b := b + eps) (lam := lam) hlam_pos
        (by linarith [heps_lt_lam]) hb_eps_lt
    refine ⟨eps, heps_pos, tau, htau_cd, htau_eq, ?_⟩
    intro t
    rw [norm_smul, Real.norm_eq_abs]
    exact lt_of_le_of_lt
      (mul_le_mul_of_nonneg_right (htau_bound t) (norm_nonneg x)) hprod




omit [T2Space M] [SigmaCompactSpace M] in
lemma radial_clip_contMDiff
    (g : SmoothRiemannianMetric I M) (p : M) (x : E) (tau : ℝ → ℝ)
    (htau : ContDiff ℝ (∞ : WithTop ℕ∞) tau)
    (hradius : ∀ t : ℝ, ‖tau t • x‖ < expMapC2Radius (I := I) g p) :
    ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞)
      (fun t : ℝ => (expMap (I := I) g p
        (show TangentSpace I p from (tau t • x)) : M)) := by
  intro t
  have htauMD : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (∞ : WithTop ℕ∞) tau := by
    rw [contMDiff_iff_contDiff]
    exact htau
  have hsmul : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (∞ : WithTop ℕ∞)
      (fun t : ℝ => tau t • x) :=
    htauMD.smul contMDiff_const
  have hexpC2 : ContMDiffAt 𝓘(ℝ, E) I (2 : ℕ∞)
      (fun b : E => (expMap (I := I) g p (show TangentSpace I p from b) : M))
      (tau t • x) :=
    expMap_contMDiffAt2_of_norm_lt_radius (I := I) g p (hradius t)
  simpa using hexpC2.comp t (hsmul.contMDiffAt.of_le ENat.LEInfty.out)




omit [T2Space M] [SigmaCompactSpace M] in
lemma exists_radial_ext
    (g : SmoothRiemannianMetric I M) (p : M) (x : E) {b : ℝ}
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hx : ‖x‖ < expMapC2Radius (I := I) g p) :
    ∃ gamma : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) gamma ∧
      Set.EqOn gamma (radialCurve (I := I) g p x) (Set.Icc 0 b) := by
  obtain ⟨tau, htau, htau_eq, hradius⟩ :=
    exists_radial_clip (I := I) g p x hb0 hb1 hx
  refine ⟨fun t : ℝ => (expMap (I := I) g p
    (show TangentSpace I p from (tau t • x)) : M), ?_, ?_⟩
  · exact radial_clip_contMDiff (I := I) g p x tau htau hradius
  · intro t ht
    change expMap (I := I) g p (show TangentSpace I p from (tau t • x)) =
      radialCurve (I := I) g p x t
    rw [htau_eq ht]
    rfl



omit [T2Space M] [SigmaCompactSpace M] in
lemma exists_rext_nbhd
    (g : SmoothRiemannianMetric I M) (p : M) (x : E) {b : ℝ}
    (hb1 : b ≤ 1)
    (hx : ‖x‖ < expMapC2Radius (I := I) g p) :
    ∃ eps : ℝ, 0 < eps ∧ ∃ gamma : ℝ → M,
      ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) gamma ∧
      Set.EqOn gamma (radialCurve (I := I) g p x) (Set.Icc (-eps) (b + eps)) := by
  obtain ⟨eps, heps, tau, htau, htau_eq, hradius⟩ :=
    exists_rclip_nbhd (I := I) g p x hb1 hx
  refine ⟨eps, heps, fun t : ℝ => (expMap (I := I) g p
    (show TangentSpace I p from (tau t • x)) : M), ?_, ?_⟩
  · exact radial_clip_contMDiff (I := I) g p x tau htau hradius
  · intro t ht
    change expMap (I := I) g p (show TangentSpace I p from (tau t • x)) =
      radialCurve (I := I) g p x t
    rw [htau_eq ht]
    rfl



omit [T2Space M] [SigmaCompactSpace M] in
theorem radial_speed_sq_eq
    (g : SmoothRiemannianMetric I M) (p : M) (x : E)
    (hx : ‖x‖ < expMapC2Radius (I := I) g p) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    g.inner (radialCurve (I := I) g p x t)
      (curveVelocity (I := I) (radialCurve (I := I) g p x) t)
      (curveVelocity (I := I) (radialCurve (I := I) g p x) t) =
        g.inner p x x := by
  simpa [radialCurve, curveVelocity] using
    (DifferentialGeometry.Geometry.Riemannian.radialSpeedSq_eq_inner
      (I := I) g p x hx t ht)



omit [T2Space M] [SigmaCompactSpace M] in
theorem radial_speed_le
    (g : SmoothRiemannianMetric I M) (p : M) (x : E)
    (hx : ‖x‖ < expMapC2Radius (I := I) g p) {Vb b : ℝ}
    (hb : b ≤ 1) (hVb : Real.sqrt (g.inner p x x) ≤ Vb) :
    ∀ t ∈ Ioo (0 : ℝ) b,
      Real.sqrt (g.inner (radialCurve (I := I) g p x t)
        (curveVelocity (I := I) (radialCurve (I := I) g p x) t)
        (curveVelocity (I := I) (radialCurve (I := I) g p x) t)) ≤ Vb := by
  intro t ht
  have ht01 : t ∈ Ioo (0 : ℝ) 1 := ⟨ht.1, lt_of_lt_of_le ht.2 hb⟩
  rw [radial_speed_sq_eq (I := I) g p x hx ht01]
  exact hVb



omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
private theorem exists_gON_tangentBasis_E
    (g : SmoothRiemannianMetric I M) (y : M) :
    ∃ basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I y),
      ∀ i j, g.inner y (basis i) (basis j) = if i = j then (1 : ℝ) else 0 := by
  simpa [show Module.finrank ℝ (TangentSpace I y) = Module.finrank ℝ E from rfl]
    using DifferentialGeometry.Integral.Connection.exists_gOrthonormalBasis
      (I := I) g y




omit [SigmaCompactSpace M] in
theorem exists_jacobi_Ioo
    (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ r : ℝ, 0 < r ∧ ∀ x w : E, ‖x‖ < r → ‖w‖ < r → ∀ {b : ℝ}, b ≤ 1 →
      ∀ t ∈ Ioo (0 : ℝ) b,
        IsJacobiAt (I := I) g (radialCurve (I := I) g p x)
          (radialJacobiField (I := I) g p x w) t := by
  obtain ⟨r, hr, hJac⟩ := exists_radialJacobi_radius (I := I) g p
  refine ⟨r, hr, ?_⟩
  intro x w hx hw b hb t ht
  have ht01 : t ∈ Ioo (0 : ℝ) 1 := ⟨ht.1, lt_of_lt_of_le ht.2 hb⟩
  simpa [radialCurve] using hJac x w hx hw t ht01



omit [T2Space (TangentBundle I M)] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem radialJacobi_ode_of_curv
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E) {K b : ℝ}
    (hJac : ∀ t ∈ Ico (0 : ℝ) b,
      IsJacobiAt (I := I) g (radialCurve (I := I) g p x)
        (radialJacobiField (I := I) g p x w) t)
    (hcurv : ∀ t ∈ Ico (0 : ℝ) b,
      g.inner (radialCurve (I := I) g p x t)
        ((DifferentialGeometry.Integral.Connection.riemannOp
          (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g)
            (radialCurve (I := I) g p x t))
          (radialJacobiField (I := I) g p x w t)
          (curveVelocity (I := I) (radialCurve (I := I) g p x) t)
          (curveVelocity (I := I) (radialCurve (I := I) g p x) t))
        ((DifferentialGeometry.Integral.Connection.riemannOp
          (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g)
            (radialCurve (I := I) g p x t))
          (radialJacobiField (I := I) g p x w t)
          (curveVelocity (I := I) (radialCurve (I := I) g p x) t)
          (curveVelocity (I := I) (radialCurve (I := I) g p x) t))
        ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
          (radialJacobiField (I := I) g p x w t)
          (radialJacobiField (I := I) g p x w t)) :
    ∀ t ∈ Ico (0 : ℝ) b,
      g.inner (radialCurve (I := I) g p x t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) s) t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) s) t)
      ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
        (radialJacobiField (I := I) g p x w t)
        (radialJacobiField (I := I) g p x w t) := by
  intro t ht
  exact ode_bound_of_isJacobiAt (I := I) g (radialCurve (I := I) g p x)
    (radialJacobiField (I := I) g p x w) (K := K) (t := t) (hJac t ht)
    (hcurv t ht)





omit [T2Space (TangentBundle I M)] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem ode_Ico_of_Ioo_zero
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E) {K b : ℝ}
    (hJac : ∀ t ∈ Ioo (0 : ℝ) b,
      IsJacobiAt (I := I) g (radialCurve (I := I) g p x)
        (radialJacobiField (I := I) g p x w) t)
    (hcurv : ∀ t ∈ Ioo (0 : ℝ) b,
      g.inner (radialCurve (I := I) g p x t)
        ((DifferentialGeometry.Integral.Connection.riemannOp
          (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g)
            (radialCurve (I := I) g p x t))
          (radialJacobiField (I := I) g p x w t)
          (curveVelocity (I := I) (radialCurve (I := I) g p x) t)
          (curveVelocity (I := I) (radialCurve (I := I) g p x) t))
        ((DifferentialGeometry.Integral.Connection.riemannOp
          (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g)
            (radialCurve (I := I) g p x t))
          (radialJacobiField (I := I) g p x w t)
          (curveVelocity (I := I) (radialCurve (I := I) g p x) t)
          (curveVelocity (I := I) (radialCurve (I := I) g p x) t))
        ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
          (radialJacobiField (I := I) g p x w t)
          (radialJacobiField (I := I) g p x w t))
    (h0 :
      g.inner (radialCurve (I := I) g p x 0)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) s) 0)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) s) 0)
      ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x 0)
        (radialJacobiField (I := I) g p x w 0)
        (radialJacobiField (I := I) g p x w 0)) :
    ∀ t ∈ Ico (0 : ℝ) b,
      g.inner (radialCurve (I := I) g p x t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) s) t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) s) t)
      ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
        (radialJacobiField (I := I) g p x w t)
        (radialJacobiField (I := I) g p x w t) := by
  intro t ht
  by_cases ht0 : t = 0
  · subst t
    simpa using h0
  · have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
    exact ode_bound_of_isJacobiAt (I := I) g (radialCurve (I := I) g p x)
      (radialJacobiField (I := I) g p x w) (K := K) (t := t)
      (hJac t ⟨htpos, ht.2⟩) (hcurv t ⟨htpos, ht.2⟩)



omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem ode_Ico_of_Ioo_d2
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E) {K b : ℝ}
    (hJac : ∀ t ∈ Ioo (0 : ℝ) b,
      IsJacobiAt (I := I) g (radialCurve (I := I) g p x)
        (radialJacobiField (I := I) g p x w) t)
    (hcurv : ∀ t ∈ Ioo (0 : ℝ) b,
      g.inner (radialCurve (I := I) g p x t)
        ((DifferentialGeometry.Integral.Connection.riemannOp
          (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g)
            (radialCurve (I := I) g p x t))
          (radialJacobiField (I := I) g p x w t)
          (curveVelocity (I := I) (radialCurve (I := I) g p x) t)
          (curveVelocity (I := I) (radialCurve (I := I) g p x) t))
        ((DifferentialGeometry.Integral.Connection.riemannOp
          (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g)
            (radialCurve (I := I) g p x t))
          (radialJacobiField (I := I) g p x w t)
          (curveVelocity (I := I) (radialCurve (I := I) g p x) t)
          (curveVelocity (I := I) (radialCurve (I := I) g p x) t))
        ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
          (radialJacobiField (I := I) g p x w t)
          (radialJacobiField (I := I) g p x w t))
    (hD2 :
      covDerivAlong (I := I) g (radialCurve (I := I) g p x)
        (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (radialJacobiField (I := I) g p x w) s) 0 = 0) :
    ∀ t ∈ Ico (0 : ℝ) b,
      g.inner (radialCurve (I := I) g p x t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) s) t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) s) t)
      ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
        (radialJacobiField (I := I) g p x w t)
        (radialJacobiField (I := I) g p x w t) := by
  refine ode_Ico_of_Ioo_zero (I := I) g p x w hJac hcurv ?_
  rw [hD2, radialJacobi_zero]
  change
    g.inner (radialCurve (I := I) g p x 0)
        (0 : TangentSpace I (radialCurve (I := I) g p x 0))
        (0 : TangentSpace I (radialCurve (I := I) g p x 0)) ≤
      K ^ 2 * g.inner (radialCurve (I := I) g p x 0)
        (0 : TangentSpace I (radialCurve (I := I) g p x 0))
        (0 : TangentSpace I (radialCurve (I := I) g p x 0))
  have hz :
      g.inner (radialCurve (I := I) g p x 0)
        (0 : TangentSpace I (radialCurve (I := I) g p x 0))
        (0 : TangentSpace I (radialCurve (I := I) g p x 0)) = 0 := by
    rw [map_zero]
  rw [hz]
  rw [mul_zero]



omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem d2_zero_of_jac0
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E)
    (hJac0 : IsJacobiAt (I := I) g (radialCurve (I := I) g p x)
      (radialJacobiField (I := I) g p x w) 0) :
    covDerivAlong (I := I) g (radialCurve (I := I) g p x)
      (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
        (radialJacobiField (I := I) g p x w) s) 0 = 0 := by
  unfold IsJacobiAt at hJac0
  rw [radialJacobi_zero] at hJac0
  set D : TangentSpace I (radialCurve (I := I) g p x 0) :=
    covDerivAlong (I := I) g (radialCurve (I := I) g p x)
      (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
        (radialJacobiField (I := I) g p x w) s) 0 with hD_def
  set C : TangentSpace I (radialCurve (I := I) g p x 0) :=
    ((DifferentialGeometry.Integral.Connection.riemannOp
        (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g)
          (radialCurve (I := I) g p x 0))
        (0 : TangentSpace I (radialCurve (I := I) g p x 0))
        (curveVelocity (I := I) (radialCurve (I := I) g p x) 0)
        (curveVelocity (I := I) (radialCurve (I := I) g p x) 0)) with hC_def
  change D + C = 0 at hJac0
  have hCzero : C = 0 := by
    rw [hC_def]
    rw [map_zero]
    rw [ContinuousLinearMap.zero_apply, ContinuousLinearMap.zero_apply]
  rw [hCzero, add_zero] at hJac0
  exact hJac0




omit [SigmaCompactSpace M] in
theorem exists_ode_Ico
    (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ r : ℝ, 0 < r ∧ ∀ x w : E, ‖x‖ < r → ‖w‖ < r → ∀ {K b : ℝ}, b ≤ 1 →
      (∀ t ∈ Ioo (0 : ℝ) b,
        g.inner (radialCurve (I := I) g p x t)
          ((DifferentialGeometry.Integral.Connection.riemannOp
            (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g)
              (radialCurve (I := I) g p x t))
            (radialJacobiField (I := I) g p x w t)
            (curveVelocity (I := I) (radialCurve (I := I) g p x) t)
            (curveVelocity (I := I) (radialCurve (I := I) g p x) t))
          ((DifferentialGeometry.Integral.Connection.riemannOp
            (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g)
              (radialCurve (I := I) g p x t))
            (radialJacobiField (I := I) g p x w t)
            (curveVelocity (I := I) (radialCurve (I := I) g p x) t)
            (curveVelocity (I := I) (radialCurve (I := I) g p x) t))
          ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
            (radialJacobiField (I := I) g p x w t)
            (radialJacobiField (I := I) g p x w t)) →
      (g.inner (radialCurve (I := I) g p x 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) s) 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) s) 0)
        ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x 0)
          (radialJacobiField (I := I) g p x w 0)
          (radialJacobiField (I := I) g p x w 0)) →
      ∀ t ∈ Ico (0 : ℝ) b,
        g.inner (radialCurve (I := I) g p x t)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) s) t)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) s) t)
        ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
          (radialJacobiField (I := I) g p x w t)
          (radialJacobiField (I := I) g p x w t) := by
  obtain ⟨r, hr, hJac⟩ := exists_jacobi_Ioo (I := I) g p
  refine ⟨r, hr, ?_⟩
  intro x w hx hw K b hb hcurv h0
  exact ode_Ico_of_Ioo_zero (I := I) g p x w (K := K) (b := b)
    (hJac x w hx hw hb) hcurv h0


omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
private lemma inner_self_nonneg
    (g : SmoothRiemannianMetric I M) {q : M} (u : TangentSpace I q) :
    0 <= g.inner q u u := by
  rcases eq_or_ne u 0 with hu | hu
  · simp [hu]
  · exact (g.pos q u hu).le


omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
private lemma inner_sq_le_of_sqrt_le
    (g : SmoothRiemannianMetric I M) {q : M} {u v : TangentSpace I q} {K : Real}
    (hK : 0 ≤ K)
    (h : Real.sqrt (g.inner q u u) ≤ K * Real.sqrt (g.inner q v v)) :
    g.inner q u u ≤ K ^ 2 * g.inner q v v := by
  have hu_nn : 0 ≤ g.inner q u u := inner_self_nonneg (I := I) g u
  have hv_nn : 0 ≤ g.inner q v v := inner_self_nonneg (I := I) g v
  have hrhs_nn : 0 ≤ K * Real.sqrt (g.inner q v v) :=
    mul_nonneg hK (Real.sqrt_nonneg _)
  have hsq :
      (Real.sqrt (g.inner q u u)) ^ 2 ≤
        (K * Real.sqrt (g.inner q v v)) ^ 2 :=
    (sq_le_sq₀ (Real.sqrt_nonneg _) hrhs_nn).2 h
  calc
    g.inner q u u = (Real.sqrt (g.inner q u u)) ^ 2 := by
      rw [Real.sq_sqrt hu_nn]
    _ ≤ (K * Real.sqrt (g.inner q v v)) ^ 2 := hsq
    _ = K ^ 2 * g.inner q v v := by
      rw [mul_pow, Real.sq_sqrt hv_nn]


private def radialCurvTerm
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E) (t : Real) :
    TangentSpace I (radialCurve (I := I) g p x t) :=
  (DifferentialGeometry.Integral.Connection.riemannOp
    (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g)
      (radialCurve (I := I) g p x t))
    (radialJacobiField (I := I) g p x w t)
    (curveVelocity (I := I) (radialCurve (I := I) g p x) t)
    (curveVelocity (I := I) (radialCurve (I := I) g p x) t)


private def radialCurvTermFlat
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E) (t : Real) :
    Tensor0SBundle.Tensor0SSpace 1 I (radialCurve (I := I) g p x t) :=
  Tensor0SBundle.dualToCotangent_gen (I := I)
    (Tensor0SBundle.tangentFlatLinear_gen (I := I) g
      (radialCurve (I := I) g p x t)
      (radialCurvTerm (I := I) g p x w t))



omit [T2Space (TangentBundle I M)] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private theorem radialCurvTermFlat_inner
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E) (t : Real) :
    Tensor0SBundle.cotangentInner_gen (I := I) g
      (radialCurve (I := I) g p x t)
      (radialCurvTermFlat (I := I) g p x w t)
      (radialCurvTermFlat (I := I) g p x w t) =
        g.inner (radialCurve (I := I) g p x t)
          (radialCurvTerm (I := I) g p x w t)
          (radialCurvTerm (I := I) g p x w t) := by
  simpa [radialCurvTermFlat] using
    (Tensor0SBundle.cotangentInner_dualToCotangent_tangentFlat_gen
      (I := I) g (radialCurve (I := I) g p x t)
      (radialCurvTerm (I := I) g p x w t)
      (radialCurvTerm (I := I) g p x w t))



omit [T2Space (TangentBundle I M)] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private theorem radialCurvTermFlat_apply_eq_metricRm04StdAt
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E) (t : Real)
    (W : TangentSpace I (radialCurve (I := I) g p x t)) :
    radialCurvTermFlat (I := I) g p x w t (fun _ : Fin 1 => W) =
      DifferentialGeometry.Integral.Connection.metricRm04StdAt
        (I := I) (M := M) g (radialCurve (I := I) g p x t)
        (radialJacobiField (I := I) g p x w t)
        (curveVelocity (I := I) (radialCurve (I := I) g p x) t)
        (curveVelocity (I := I) (radialCurve (I := I) g p x) t) W := by
  have hcov :=
    DifferentialGeometry.leviCivita_contMDiffCovariantDerivativeLocally (I := I) g
  rw [DifferentialGeometry.Integral.Connection.metricRm04StdAt_apply,
    DifferentialGeometry.metricRm04At_eq_riemannCurvature04At,
    DifferentialGeometry.Integral.Connection.CovariantDerivative.riemannCurvature04At_apply_const,
    DifferentialGeometry.riemannCurvatureAux_tangentConst_eq_riemannOp
      (cov := DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g)
      (hcov := hcov)]
  unfold radialCurvTermFlat radialCurvTerm
  rw [Tensor0SBundle.dualToCotangent_apply_gen,
    Tensor0SBundle.tangentFlatLinear_apply_gen]
  exact g.symm (radialCurve (I := I) g p x t)
    (radialCurvTerm (I := I) g p x w t) W



omit [T2Space (TangentBundle I M)] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private theorem radialCurvTermFlat_component_eq_metricRm04StdAt
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E) (t : Real)
    (basis : Module.Basis Idx Real (TangentSpace I (radialCurve (I := I) g p x t)))
    (i : Idx) :
    Tensor0SBundle.component0S (I := I) basis
        (radialCurvTermFlat (I := I) g p x w t) (fun _ : Fin 1 => i) =
      DifferentialGeometry.Integral.Connection.metricRm04StdAt
        (I := I) (M := M) g (radialCurve (I := I) g p x t)
        (radialJacobiField (I := I) g p x w t)
        (curveVelocity (I := I) (radialCurve (I := I) g p x) t)
        (curveVelocity (I := I) (radialCurve (I := I) g p x) t)
        (basis i) := by
  rw [Tensor0SBundle.component0S_apply]
  exact radialCurvTermFlat_apply_eq_metricRm04StdAt (I := I) g p x w t (basis i)



omit [T2Space (TangentBundle I M)] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private theorem radialCurvTermFlat_normSq_eq_cotangentInner
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E) (t : Real) :
    Tensor0SBundle.normSq0S (I := I) g (radialCurve (I := I) g p x t) 1
        (radialCurvTermFlat (I := I) g p x w t) =
      Tensor0SBundle.cotangentInner_gen (I := I) g
        (radialCurve (I := I) g p x t)
        (radialCurvTermFlat (I := I) g p x w t)
        (radialCurvTermFlat (I := I) g p x w t) := by
  rw [Tensor0SBundle.normSq0S_eq_inner,
    Tensor0SBundle.inner0S_one_eq_cotangent]
  rfl



omit [T2Space (TangentBundle I M)] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem abs_flat_apply_le_rm04
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E) (t : Real)
    (basis : Module.Basis Idx Real (TangentSpace I (radialCurve (I := I) g p x t)))
    (hON : ∀ i j : Idx,
      g.inner (radialCurve (I := I) g p x t) (basis i) (basis j) =
        if i = j then (1 : Real) else 0)
    (W : TangentSpace I (radialCurve (I := I) g p x t)) :
    |radialCurvTermFlat (I := I) g p x w t (fun _ : Fin 1 => W)| ≤
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
        (radialCurve (I := I) g p x t) 4
        (DifferentialGeometry.Integral.Connection.metricRm04At
          (I := I) (M := M) g (radialCurve (I := I) g p x t))) *
      ∏ a : Fin 4, Real.sqrt (g.inner (radialCurve (I := I) g p x t)
        ((DifferentialGeometry.Integral.Connection.vec4 (I := I)
          (radialJacobiField (I := I) g p x w t)
          (curveVelocity (I := I) (radialCurve (I := I) g p x) t)
          (curveVelocity (I := I) (radialCurve (I := I) g p x) t)
          W) a)
        ((DifferentialGeometry.Integral.Connection.vec4 (I := I)
          (radialJacobiField (I := I) g p x w t)
          (curveVelocity (I := I) (radialCurve (I := I) g p x) t)
          (curveVelocity (I := I) (radialCurve (I := I) g p x) t)
          W) a)) := by
  have hCS := Tensor0SBundle.abs_apply_le_sqrt_normSq0S
    (I := I) g (radialCurve (I := I) g p x t) 4 basis hON
    (DifferentialGeometry.Integral.Connection.metricRm04At
      (I := I) (M := M) g (radialCurve (I := I) g p x t))
    (DifferentialGeometry.Integral.Connection.vec4 (I := I)
      (radialJacobiField (I := I) g p x w t)
      (curveVelocity (I := I) (radialCurve (I := I) g p x) t)
      (curveVelocity (I := I) (radialCurve (I := I) g p x) t)
      W)
  rw [radialCurvTermFlat_apply_eq_metricRm04StdAt (I := I) g p x w t W]
  simpa [DifferentialGeometry.Integral.Connection.metricRm04StdAt_apply] using hCS




omit [T2Space (TangentBundle I M)] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem radialCurvTermFlat_normSq_le_card
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E) (t : Real)
    (basis : Module.Basis Idx Real (TangentSpace I (radialCurve (I := I) g p x t)))
    (hON : ∀ i j : Idx,
      g.inner (radialCurve (I := I) g p x t) (basis i) (basis j) =
        if i = j then (1 : Real) else 0)
    (B : Real) (hBnn : 0 ≤ B)
    (hB : ∀ i : Idx,
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
        (radialCurve (I := I) g p x t) 4
        (DifferentialGeometry.Integral.Connection.metricRm04At
          (I := I) (M := M) g (radialCurve (I := I) g p x t))) *
      ∏ a : Fin 4, Real.sqrt (g.inner (radialCurve (I := I) g p x t)
        ((DifferentialGeometry.Integral.Connection.vec4 (I := I)
          (radialJacobiField (I := I) g p x w t)
          (curveVelocity (I := I) (radialCurve (I := I) g p x) t)
          (curveVelocity (I := I) (radialCurve (I := I) g p x) t)
          (basis i)) a)
        ((DifferentialGeometry.Integral.Connection.vec4 (I := I)
          (radialJacobiField (I := I) g p x w t)
          (curveVelocity (I := I) (radialCurve (I := I) g p x) t)
          (curveVelocity (I := I) (radialCurve (I := I) g p x) t)
          (basis i)) a)) ≤ B) :
    Tensor0SBundle.normSq0S (I := I) g (radialCurve (I := I) g p x t) 1
        (radialCurvTermFlat (I := I) g p x w t) ≤
      (Fintype.card (Fin 1 -> Idx) : Real) * B ^ 2 := by
  classical
  have hinv :
      Tensor0SBundle.MetricInverseInBasis_gen (I := I) g
        (radialCurve (I := I) g p x t) basis
        (Tensor0SBundle.identityInvMetric (Idx := Idx)) :=
    DifferentialGeometry.Integral.Connection.metricInverseInBasis_of_orthonormal
      (I := I) g basis hON
  refine Tensor0SBundle.normSq0S_le_card_of_component_bound
    (I := I) g (radialCurve (I := I) g p x t) 1 basis hinv
    (radialCurvTermFlat (I := I) g p x w t) B hBnn ?_
  intro slots
  have hslots :
      (fun a : Fin 1 => basis (slots a)) =
        (fun _ : Fin 1 => basis (slots 0)) := by
    funext a
    exact congrArg basis (congrArg slots (Subsingleton.elim a (0 : Fin 1)))
  have happly := abs_flat_apply_le_rm04
    (I := I) g p x w t basis hON (basis (slots 0))
  calc
    |Tensor0SBundle.component0S (I := I) basis
        (radialCurvTermFlat (I := I) g p x w t) slots|
        = |radialCurvTermFlat (I := I) g p x w t
            (fun _ : Fin 1 => basis (slots 0))| := by
          rw [Tensor0SBundle.component0S_apply, hslots]
    _ ≤ Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (radialCurve (I := I) g p x t) 4
          (DifferentialGeometry.Integral.Connection.metricRm04At
            (I := I) (M := M) g (radialCurve (I := I) g p x t))) *
        ∏ a : Fin 4, Real.sqrt (g.inner (radialCurve (I := I) g p x t)
          ((DifferentialGeometry.Integral.Connection.vec4 (I := I)
            (radialJacobiField (I := I) g p x w t)
            (curveVelocity (I := I) (radialCurve (I := I) g p x) t)
            (curveVelocity (I := I) (radialCurve (I := I) g p x) t)
            (basis (slots 0))) a)
          ((DifferentialGeometry.Integral.Connection.vec4 (I := I)
            (radialJacobiField (I := I) g p x w t)
            (curveVelocity (I := I) (radialCurve (I := I) g p x) t)
            (curveVelocity (I := I) (radialCurve (I := I) g p x) t)
            (basis (slots 0))) a)) := happly
    _ ≤ B := hB (slots 0)



omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
private theorem radialSlotProd_basis_le
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) {q : M}
    (basis : Module.Basis Idx Real (TangentSpace I q))
    (hON : ∀ i j : Idx,
      g.inner q (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (J V : TangentSpace I q) (i : Idx) :
    ∏ a : Fin 4, Real.sqrt (g.inner q
        ((DifferentialGeometry.Integral.Connection.vec4 (I := I)
          J V V (basis i)) a)
        ((DifferentialGeometry.Integral.Connection.vec4 (I := I)
          J V V (basis i)) a)) ≤
      Real.sqrt (g.inner q J J) * (Real.sqrt (g.inner q V V)) ^ 2 := by
  have hunit : Real.sqrt (g.inner q (basis i) (basis i)) = 1 := by
    rw [hON i i]
    simp
  rw [Fin.prod_univ_four]
  simp [DifferentialGeometry.Integral.Connection.vec4, hunit, pow_two]
  ring_nf
  exact le_rfl



omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
private theorem radialSlotBound_basis_le
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) {q : M}
    (basis : Module.Basis Idx Real (TangentSpace I q))
    (hON : ∀ i j : Idx,
      g.inner q (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (R Jb Vb : Real) (hRnn : 0 ≤ R) (hJb : 0 ≤ Jb) (hVb : 0 ≤ Vb)
    (J V : TangentSpace I q)
    (hJ : Real.sqrt (g.inner q J J) ≤ Jb)
    (hV : Real.sqrt (g.inner q V V) ≤ Vb) (i : Idx) :
    R * (∏ a : Fin 4, Real.sqrt (g.inner q
        ((DifferentialGeometry.Integral.Connection.vec4 (I := I)
          J V V (basis i)) a)
        ((DifferentialGeometry.Integral.Connection.vec4 (I := I)
          J V V (basis i)) a))) ≤
      R * Jb * Vb ^ 2 := by
  have hprod := radialSlotProd_basis_le (I := I) g basis hON J V i
  have hVsq :
      (Real.sqrt (g.inner q V V)) ^ 2 ≤ Vb ^ 2 := by
    have habs :
        |Real.sqrt (g.inner q V V)| ≤ |Vb| := by
      simpa [abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg hVb] using hV
    exact sq_le_sq.mpr habs
  have hprod_bound :
      ∏ a : Fin 4, Real.sqrt (g.inner q
          ((DifferentialGeometry.Integral.Connection.vec4 (I := I)
            J V V (basis i)) a)
          ((DifferentialGeometry.Integral.Connection.vec4 (I := I)
            J V V (basis i)) a)) ≤
        Jb * Vb ^ 2 := by
    calc
      ∏ a : Fin 4, Real.sqrt (g.inner q
          ((DifferentialGeometry.Integral.Connection.vec4 (I := I)
            J V V (basis i)) a)
          ((DifferentialGeometry.Integral.Connection.vec4 (I := I)
            J V V (basis i)) a))
          ≤ Real.sqrt (g.inner q J J) *
              (Real.sqrt (g.inner q V V)) ^ 2 := hprod
      _ ≤ Jb * Vb ^ 2 := by
          exact mul_le_mul hJ hVsq (sq_nonneg _) hJb
  calc
    R * (∏ a : Fin 4, Real.sqrt (g.inner q
        ((DifferentialGeometry.Integral.Connection.vec4 (I := I)
          J V V (basis i)) a)
        ((DifferentialGeometry.Integral.Connection.vec4 (I := I)
          J V V (basis i)) a)))
        ≤ R * (Jb * Vb ^ 2) := mul_le_mul_of_nonneg_left hprod_bound hRnn
    _ = R * Jb * Vb ^ 2 := by ring



omit [T2Space (TangentBundle I M)] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem radialCurvTermFlat_normSq_le_card_of_bounds
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E) (t : Real)
    (basis : Module.Basis Idx Real (TangentSpace I (radialCurve (I := I) g p x t)))
    (hON : ∀ i j : Idx,
      g.inner (radialCurve (I := I) g p x t) (basis i) (basis j) =
        if i = j then (1 : Real) else 0)
    (Jb Vb : Real) (hJb : 0 ≤ Jb) (hVb : 0 ≤ Vb)
    (hJ : Real.sqrt (g.inner (radialCurve (I := I) g p x t)
      (radialJacobiField (I := I) g p x w t)
      (radialJacobiField (I := I) g p x w t)) ≤ Jb)
    (hV : Real.sqrt (g.inner (radialCurve (I := I) g p x t)
      (curveVelocity (I := I) (radialCurve (I := I) g p x) t)
      (curveVelocity (I := I) (radialCurve (I := I) g p x) t)) ≤ Vb) :
    Tensor0SBundle.normSq0S (I := I) g (radialCurve (I := I) g p x t) 1
        (radialCurvTermFlat (I := I) g p x w t) ≤
      (Fintype.card (Fin 1 -> Idx) : Real) *
        (Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (radialCurve (I := I) g p x t) 4
          (DifferentialGeometry.Integral.Connection.metricRm04At
            (I := I) (M := M) g (radialCurve (I := I) g p x t))) *
          Jb * Vb ^ 2) ^ 2 := by
  classical
  set R : Real := Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
    (radialCurve (I := I) g p x t) 4
    (DifferentialGeometry.Integral.Connection.metricRm04At
      (I := I) (M := M) g (radialCurve (I := I) g p x t)))
  have hRnn : 0 ≤ R := by
    simp [R]
  have hBnn : 0 ≤ R * Jb * Vb ^ 2 :=
    mul_nonneg (mul_nonneg hRnn hJb) (pow_nonneg hVb 2)
  refine radialCurvTermFlat_normSq_le_card
    (I := I) g p x w t basis hON (R * Jb * Vb ^ 2) hBnn ?_
  intro i
  simpa [R] using
    radialSlotBound_basis_le (I := I) g basis hON R Jb Vb hRnn hJb hVb
      (radialJacobiField (I := I) g p x w t)
      (curveVelocity (I := I) (radialCurve (I := I) g p x) t) hJ hV i


private theorem sqrt_le_sqrt_mul_of_sq_le {A C B : Real}
    (hC : 0 ≤ C) (hB : 0 ≤ B) (h : A ≤ C * B ^ 2) :
    Real.sqrt A ≤ Real.sqrt C * B := by
  calc
    Real.sqrt A ≤ Real.sqrt (C * B ^ 2) := Real.sqrt_le_sqrt h
    _ = Real.sqrt C * Real.sqrt (B ^ 2) := Real.sqrt_mul hC _
    _ = Real.sqrt C * B := by rw [Real.sqrt_sq hB]




omit [T2Space (TangentBundle I M)] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem radialCurvTermFlat_sqrt_le_card_of_velocity_bound
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E) (t : Real)
    (basis : Module.Basis Idx Real (TangentSpace I (radialCurve (I := I) g p x t)))
    (hON : ∀ i j : Idx,
      g.inner (radialCurve (I := I) g p x t) (basis i) (basis j) =
        if i = j then (1 : Real) else 0)
    (Vb : Real) (hVb : 0 ≤ Vb)
    (hV : Real.sqrt (g.inner (radialCurve (I := I) g p x t)
      (curveVelocity (I := I) (radialCurve (I := I) g p x) t)
      (curveVelocity (I := I) (radialCurve (I := I) g p x) t)) ≤ Vb) :
    Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
        (radialCurve (I := I) g p x t) 1
        (radialCurvTermFlat (I := I) g p x w t)) ≤
      Real.sqrt ((Fintype.card (Fin 1 -> Idx) : Real)) *
        (Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (radialCurve (I := I) g p x t) 4
          (DifferentialGeometry.Integral.Connection.metricRm04At
            (I := I) (M := M) g (radialCurve (I := I) g p x t))) *
          Real.sqrt (g.inner (radialCurve (I := I) g p x t)
            (radialJacobiField (I := I) g p x w t)
            (radialJacobiField (I := I) g p x w t)) *
          Vb ^ 2) := by
  classical
  set Jb : Real := Real.sqrt (g.inner (radialCurve (I := I) g p x t)
    (radialJacobiField (I := I) g p x w t)
    (radialJacobiField (I := I) g p x w t))
  set R : Real := Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
    (radialCurve (I := I) g p x t) 4
    (DifferentialGeometry.Integral.Connection.metricRm04At
      (I := I) (M := M) g (radialCurve (I := I) g p x t)))
  have hJb : 0 ≤ Jb := by
    simp [Jb]
  have hBnn : 0 ≤ R * Jb * Vb ^ 2 := by
    exact mul_nonneg (mul_nonneg (by simp [R]) hJb) (pow_nonneg hVb 2)
  have hsq := radialCurvTermFlat_normSq_le_card_of_bounds
    (I := I) g p x w t basis hON Jb Vb hJb hVb (by simp [Jb]) hV
  have hcard : 0 ≤ (Fintype.card (Fin 1 -> Idx) : Real) := by
    exact Nat.cast_nonneg _
  simpa [R, Jb] using
    sqrt_le_sqrt_mul_of_sq_le hcard hBnn hsq



omit [T2Space (TangentBundle I M)] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem radialCurvTermFlat_sqrt_le_K
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E) (t : Real)
    (basis : Module.Basis Idx Real (TangentSpace I (radialCurve (I := I) g p x t)))
    (hON : ∀ i j : Idx,
      g.inner (radialCurve (I := I) g p x t) (basis i) (basis j) =
        if i = j then (1 : Real) else 0)
    (K Vb : Real) (hVb : 0 ≤ Vb)
    (hV : Real.sqrt (g.inner (radialCurve (I := I) g p x t)
      (curveVelocity (I := I) (radialCurve (I := I) g p x) t)
      (curveVelocity (I := I) (radialCurve (I := I) g p x) t)) ≤ Vb)
    (hRm :
      Real.sqrt ((Fintype.card (Fin 1 -> Idx) : Real)) *
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (radialCurve (I := I) g p x t) 4
          (DifferentialGeometry.Integral.Connection.metricRm04At
            (I := I) (M := M) g (radialCurve (I := I) g p x t))) *
        Vb ^ 2 ≤ K) :
    Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
        (radialCurve (I := I) g p x t) 1
        (radialCurvTermFlat (I := I) g p x w t)) ≤
      K * Real.sqrt (g.inner (radialCurve (I := I) g p x t)
        (radialJacobiField (I := I) g p x w t)
        (radialJacobiField (I := I) g p x w t)) := by
  set Cn : Real := Real.sqrt ((Fintype.card (Fin 1 -> Idx) : Real))
  set Rn : Real := Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
    (radialCurve (I := I) g p x t) 4
    (DifferentialGeometry.Integral.Connection.metricRm04At
      (I := I) (M := M) g (radialCurve (I := I) g p x t)))
  set Jn : Real := Real.sqrt (g.inner (radialCurve (I := I) g p x t)
    (radialJacobiField (I := I) g p x w t)
    (radialJacobiField (I := I) g p x w t))
  have hbase := radialCurvTermFlat_sqrt_le_card_of_velocity_bound
    (I := I) g p x w t basis hON Vb hVb hV
  have hcoef : Cn * Rn * Vb ^ 2 ≤ K := by
    simpa [Cn, Rn] using hRm
  have hJn : 0 ≤ Jn := by
    simp [Jn]
  have hstep : Cn * (Rn * Jn * Vb ^ 2) ≤ K * Jn := by
    calc
      Cn * (Rn * Jn * Vb ^ 2) = (Cn * Rn * Vb ^ 2) * Jn := by ring
      _ ≤ K * Jn := mul_le_mul_of_nonneg_right hcoef hJn
  exact hbase.trans (by simpa [Cn, Rn, Jn] using hstep)



omit [NeZero (Module.finrank ℝ E)] [T2Space (TangentBundle I M)] in
omit [SigmaCompactSpace M] in
theorem curv_sq_of_flat_Ioo
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E) {K b : Real}
    (hK : 0 ≤ K)
    (hcurv : ∀ t ∈ Ioo (0 : Real) b,
      Real.sqrt (Tensor0SBundle.cotangentInner_gen (I := I) g
        (radialCurve (I := I) g p x t)
        (radialCurvTermFlat (I := I) g p x w t)
        (radialCurvTermFlat (I := I) g p x w t)) ≤
        K * Real.sqrt (g.inner (radialCurve (I := I) g p x t)
          (radialJacobiField (I := I) g p x w t)
          (radialJacobiField (I := I) g p x w t))) :
    ∀ t ∈ Ioo (0 : Real) b,
      g.inner (radialCurve (I := I) g p x t)
        (radialCurvTerm (I := I) g p x w t)
        (radialCurvTerm (I := I) g p x w t)
        ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
          (radialJacobiField (I := I) g p x w t)
          (radialJacobiField (I := I) g p x w t) := by
  intro t ht
  exact inner_sq_le_of_sqrt_le (I := I) g hK
    (by
      have h := hcurv t ht
      rw [radialCurvTermFlat_inner] at h
      exact h)



omit [NeZero (Module.finrank ℝ E)] [T2Space (TangentBundle I M)] in
omit [SigmaCompactSpace M] in
theorem curv_sq_of_fiber_Ioo
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E) {K b : Real}
    (hK : 0 ≤ K)
    (hcurv : ∀ t ∈ Ioo (0 : Real) b,
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
        (radialCurve (I := I) g p x t) 1
        (radialCurvTermFlat (I := I) g p x w t)) ≤
        K * Real.sqrt (g.inner (radialCurve (I := I) g p x t)
          (radialJacobiField (I := I) g p x w t)
          (radialJacobiField (I := I) g p x w t))) :
    ∀ t ∈ Ioo (0 : Real) b,
      g.inner (radialCurve (I := I) g p x t)
        (radialCurvTerm (I := I) g p x w t)
        (radialCurvTerm (I := I) g p x w t)
        ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
          (radialJacobiField (I := I) g p x w t)
          (radialJacobiField (I := I) g p x w t) := by
  refine curv_sq_of_flat_Ioo (I := I) g p x w hK ?_
  intro t ht
  simpa [radialCurvTermFlat_normSq_eq_cotangentInner]
    using hcurv t ht




omit [T2Space (TangentBundle I M)] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem curv_sq_of_rm04_velocity_Ioo
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E) {K Vb b : Real}
    (hK : 0 ≤ K) (hVb : 0 ≤ Vb)
    (basis : ∀ t : Real, t ∈ Ioo (0 : Real) b →
      Module.Basis Idx Real (TangentSpace I (radialCurve (I := I) g p x t)))
    (hON : ∀ t (ht : t ∈ Ioo (0 : Real) b) i j,
      g.inner (radialCurve (I := I) g p x t) (basis t ht i) (basis t ht j) =
        if i = j then (1 : Real) else 0)
    (hV : ∀ t (_ht : t ∈ Ioo (0 : Real) b),
      Real.sqrt (g.inner (radialCurve (I := I) g p x t)
        (curveVelocity (I := I) (radialCurve (I := I) g p x) t)
        (curveVelocity (I := I) (radialCurve (I := I) g p x) t)) ≤ Vb)
    (hRm : ∀ t (_ht : t ∈ Ioo (0 : Real) b),
      Real.sqrt ((Fintype.card (Fin 1 -> Idx) : Real)) *
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (radialCurve (I := I) g p x t) 4
          (DifferentialGeometry.Integral.Connection.metricRm04At
            (I := I) (M := M) g (radialCurve (I := I) g p x t))) *
        Vb ^ 2 ≤ K) :
    ∀ t ∈ Ioo (0 : Real) b,
      g.inner (radialCurve (I := I) g p x t)
        (radialCurvTerm (I := I) g p x w t)
        (radialCurvTerm (I := I) g p x w t)
        ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
          (radialJacobiField (I := I) g p x w t)
          (radialJacobiField (I := I) g p x w t) := by
  refine curv_sq_of_fiber_Ioo (I := I) g p x w hK ?_
  intro t ht
  exact radialCurvTermFlat_sqrt_le_K
    (I := I) g p x w t (basis t ht) (hON t ht) K Vb hVb
    (hV t ht) (hRm t ht)



omit [NeZero (Module.finrank ℝ E)] [T2Space (TangentBundle I M)] in
omit [SigmaCompactSpace M] in
theorem curv_sq_of_norm_Ioo
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E) {K b : Real}
    (hK : 0 ≤ K)
    (hcurv : ∀ t ∈ Ioo (0 : Real) b,
      Real.sqrt (g.inner (radialCurve (I := I) g p x t)
        (radialCurvTerm (I := I) g p x w t)
        (radialCurvTerm (I := I) g p x w t)) ≤
        K * Real.sqrt (g.inner (radialCurve (I := I) g p x t)
          (radialJacobiField (I := I) g p x w t)
          (radialJacobiField (I := I) g p x w t))) :
    ∀ t ∈ Ioo (0 : Real) b,
      g.inner (radialCurve (I := I) g p x t)
        (radialCurvTerm (I := I) g p x w t)
        (radialCurvTerm (I := I) g p x w t)
        ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
          (radialJacobiField (I := I) g p x w t)
          (radialJacobiField (I := I) g p x w t) := by
  intro t ht
  exact inner_sq_le_of_sqrt_le (I := I) g hK (hcurv t ht)



omit [SigmaCompactSpace M] in
theorem exists_ode_Ico_of_curvNorm
    (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ r : Real, 0 < r ∧ ∀ x w : E, ‖x‖ < r → ‖w‖ < r → ∀ {K b : Real},
      0 ≤ K → b ≤ 1 →
      (∀ t ∈ Ioo (0 : Real) b,
        Real.sqrt (g.inner (radialCurve (I := I) g p x t)
          (radialCurvTerm (I := I) g p x w t)
          (radialCurvTerm (I := I) g p x w t)) ≤
          K * Real.sqrt (g.inner (radialCurve (I := I) g p x t)
            (radialJacobiField (I := I) g p x w t)
            (radialJacobiField (I := I) g p x w t))) →
      (g.inner (radialCurve (I := I) g p x 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) s) 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) s) 0)
        ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x 0)
          (radialJacobiField (I := I) g p x w 0)
          (radialJacobiField (I := I) g p x w 0)) →
      ∀ t ∈ Ico (0 : Real) b,
        g.inner (radialCurve (I := I) g p x t)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) s) t)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) s) t)
        ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
          (radialJacobiField (I := I) g p x w t)
          (radialJacobiField (I := I) g p x w t) := by
  obtain ⟨r, hr, hODE⟩ := exists_ode_Ico (I := I) g p
  refine ⟨r, hr, ?_⟩
  intro x w hx hw K b hK hb hcurv h0
  exact hODE x w hx hw hb (curv_sq_of_norm_Ioo (I := I) g p x w hK hcurv) h0



omit [SigmaCompactSpace M] in
theorem exists_ode_Ico_of_flat
    (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ r : Real, 0 < r ∧ ∀ x w : E, ‖x‖ < r → ‖w‖ < r → ∀ {K b : Real},
      0 ≤ K → b ≤ 1 →
      (∀ t ∈ Ioo (0 : Real) b,
        Real.sqrt (Tensor0SBundle.cotangentInner_gen (I := I) g
          (radialCurve (I := I) g p x t)
          (radialCurvTermFlat (I := I) g p x w t)
          (radialCurvTermFlat (I := I) g p x w t)) ≤
          K * Real.sqrt (g.inner (radialCurve (I := I) g p x t)
            (radialJacobiField (I := I) g p x w t)
            (radialJacobiField (I := I) g p x w t))) →
      (g.inner (radialCurve (I := I) g p x 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) s) 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) s) 0)
        ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x 0)
          (radialJacobiField (I := I) g p x w 0)
          (radialJacobiField (I := I) g p x w 0)) →
      ∀ t ∈ Ico (0 : Real) b,
        g.inner (radialCurve (I := I) g p x t)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) s) t)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) s) t)
        ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
          (radialJacobiField (I := I) g p x w t)
          (radialJacobiField (I := I) g p x w t) := by
  obtain ⟨r, hr, hODE⟩ := exists_ode_Ico (I := I) g p
  refine ⟨r, hr, ?_⟩
  intro x w hx hw K b hK hb hcurv h0
  exact hODE x w hx hw hb (curv_sq_of_flat_Ioo (I := I) g p x w hK hcurv) h0



omit [SigmaCompactSpace M] in
theorem exists_ode_Ico_of_fiber
    (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ r : Real, 0 < r ∧ ∀ x w : E, ‖x‖ < r → ‖w‖ < r → ∀ {K b : Real},
      0 ≤ K → b ≤ 1 →
      (∀ t ∈ Ioo (0 : Real) b,
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (radialCurve (I := I) g p x t) 1
          (radialCurvTermFlat (I := I) g p x w t)) ≤
          K * Real.sqrt (g.inner (radialCurve (I := I) g p x t)
            (radialJacobiField (I := I) g p x w t)
            (radialJacobiField (I := I) g p x w t))) →
      (g.inner (radialCurve (I := I) g p x 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) s) 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) s) 0)
        ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x 0)
          (radialJacobiField (I := I) g p x w 0)
          (radialJacobiField (I := I) g p x w 0)) →
      ∀ t ∈ Ico (0 : Real) b,
        g.inner (radialCurve (I := I) g p x t)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) s) t)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) s) t)
        ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
          (radialJacobiField (I := I) g p x w t)
          (radialJacobiField (I := I) g p x w t) := by
  obtain ⟨r, hr, hODE⟩ := exists_ode_Ico_of_flat (I := I) g p
  refine ⟨r, hr, ?_⟩
  intro x w hx hw K b hK hb hcurv h0
  refine hODE x w hx hw hK hb ?_ h0
  intro t ht
  simpa [radialCurvTermFlat_normSq_eq_cotangentInner]
    using hcurv t ht




omit [SigmaCompactSpace M] in
theorem exists_ode_Ico_of_rm04_velocity
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ r : Real, 0 < r ∧ ∀ x w : E, ‖x‖ < r → ‖w‖ < r →
      ∀ {K Vb b : Real}, 0 ≤ K → 0 ≤ Vb → b ≤ 1 →
      (basis : ∀ t : Real, t ∈ Ioo (0 : Real) b →
        Module.Basis Idx Real (TangentSpace I (radialCurve (I := I) g p x t))) →
      (∀ t (ht : t ∈ Ioo (0 : Real) b) i j,
        g.inner (radialCurve (I := I) g p x t) ((basis t ht) i) ((basis t ht) j) =
          if i = j then (1 : Real) else 0) →
      (∀ t (_ht : t ∈ Ioo (0 : Real) b),
        Real.sqrt (g.inner (radialCurve (I := I) g p x t)
          (curveVelocity (I := I) (radialCurve (I := I) g p x) t)
          (curveVelocity (I := I) (radialCurve (I := I) g p x) t)) ≤ Vb) →
      (∀ t (_ht : t ∈ Ioo (0 : Real) b),
        Real.sqrt ((Fintype.card (Fin 1 -> Idx) : Real)) *
          Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
            (radialCurve (I := I) g p x t) 4
            (DifferentialGeometry.Integral.Connection.metricRm04At
              (I := I) (M := M) g (radialCurve (I := I) g p x t))) *
          Vb ^ 2 ≤ K) →
      (g.inner (radialCurve (I := I) g p x 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) s) 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) s) 0)
        ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x 0)
          (radialJacobiField (I := I) g p x w 0)
          (radialJacobiField (I := I) g p x w 0)) →
      ∀ t ∈ Ico (0 : Real) b,
        g.inner (radialCurve (I := I) g p x t)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) s) t)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) s) t)
        ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
          (radialJacobiField (I := I) g p x w t)
          (radialJacobiField (I := I) g p x w t) := by
  obtain ⟨r, hr, hODE⟩ := exists_ode_Ico (I := I) g p
  refine ⟨r, hr, ?_⟩
  intro x w hx hw K Vb b hK hVb hb basis hON hV hRm h0
  exact hODE x w hx hw hb
    (curv_sq_of_rm04_velocity_Ioo (I := I) g p x w hK hVb basis hON hV hRm) h0




omit [SigmaCompactSpace M] in
theorem exists_ode_Ico_of_rm04_launch
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ r : Real, 0 < r ∧ ∀ x w : E, ‖x‖ < r → ‖w‖ < r →
      ∀ {K Vb b : Real}, 0 ≤ K → 0 ≤ Vb → b ≤ 1 →
      Real.sqrt (g.inner p x x) ≤ Vb →
      (basis : ∀ t : Real, t ∈ Ioo (0 : Real) b →
        Module.Basis Idx Real (TangentSpace I (radialCurve (I := I) g p x t))) →
      (∀ t (ht : t ∈ Ioo (0 : Real) b) i j,
        g.inner (radialCurve (I := I) g p x t) ((basis t ht) i) ((basis t ht) j) =
          if i = j then (1 : Real) else 0) →
      (∀ t (_ht : t ∈ Ioo (0 : Real) b),
        Real.sqrt ((Fintype.card (Fin 1 -> Idx) : Real)) *
          Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
            (radialCurve (I := I) g p x t) 4
            (DifferentialGeometry.Integral.Connection.metricRm04At
              (I := I) (M := M) g (radialCurve (I := I) g p x t))) *
          Vb ^ 2 ≤ K) →
      (g.inner (radialCurve (I := I) g p x 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) s) 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) s) 0)
        ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x 0)
          (radialJacobiField (I := I) g p x w 0)
          (radialJacobiField (I := I) g p x w 0)) →
      ∀ t ∈ Ico (0 : Real) b,
        g.inner (radialCurve (I := I) g p x t)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) s) t)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) s) t)
        ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
          (radialJacobiField (I := I) g p x w t)
          (radialJacobiField (I := I) g p x w t) := by
  obtain ⟨r₀, hr₀, hODE⟩ := exists_ode_Ico_of_rm04_velocity (I := I) (Idx := Idx) g p
  refine ⟨min r₀ (expMapC2Radius (I := I) g p),
    lt_min hr₀ (DifferentialGeometry.Geometry.Riemannian.expMapC2Radius_pos
      (I := I) g p), ?_⟩
  intro x w hx hw K Vb b hK hVb hb hlaunch basis hON hRm h0
  have hx₀ : ‖x‖ < r₀ := lt_of_lt_of_le hx (min_le_left _ _)
  have hw₀ : ‖w‖ < r₀ := lt_of_lt_of_le hw (min_le_left _ _)
  have hxExp : ‖x‖ < expMapC2Radius (I := I) g p :=
    lt_of_lt_of_le hx (min_le_right _ _)
  exact hODE x w hx₀ hw₀ hK hVb hb basis hON
    (radial_speed_le (I := I) g p x hxExp hb hlaunch) hRm h0




omit [SigmaCompactSpace M] in
theorem exists_ode_Ico_of_rm04
    (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ r : Real, 0 < r ∧ ∀ x w : E, ‖x‖ < r → ‖w‖ < r →
      ∀ {K Vb b : Real}, 0 ≤ K → 0 ≤ Vb → b ≤ 1 →
      Real.sqrt (g.inner p x x) ≤ Vb →
      (∀ t (_ht : t ∈ Ioo (0 : Real) b),
        Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
            (radialCurve (I := I) g p x t) 4
            (DifferentialGeometry.Integral.Connection.metricRm04At
              (I := I) (M := M) g (radialCurve (I := I) g p x t))) *
          Vb ^ 2 ≤ K) →
      (g.inner (radialCurve (I := I) g p x 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) s) 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) s) 0)
        ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x 0)
          (radialJacobiField (I := I) g p x w 0)
          (radialJacobiField (I := I) g p x w 0)) →
      ∀ t ∈ Ico (0 : Real) b,
        g.inner (radialCurve (I := I) g p x t)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) s) t)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) s) t)
        ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
          (radialJacobiField (I := I) g p x w t)
          (radialJacobiField (I := I) g p x w t) := by
  classical
  obtain ⟨r, hr, hODE⟩ :=
    exists_ode_Ico_of_rm04_launch (I := I) (Idx := Fin (Module.finrank ℝ E)) g p
  refine ⟨r, hr, ?_⟩
  intro x w hx hw K Vb b hK hVb hb hlaunch hRm h0
  have hbasis :
      ∀ t : Real, t ∈ Ioo (0 : Real) b →
        ∃ basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ
            (TangentSpace I (radialCurve (I := I) g p x t)),
          ∀ i j,
            g.inner (radialCurve (I := I) g p x t) (basis i) (basis j) =
              if i = j then (1 : Real) else 0 := by
    intro t _ht
    exact exists_gON_tangentBasis_E (I := I) g (radialCurve (I := I) g p x t)
  choose basis hON using hbasis
  exact hODE x w hx hw hK hVb hb hlaunch basis
    (fun t ht i j => hON t ht i j) hRm h0



omit [SigmaCompactSpace M] in
theorem exists_ode_Ico_of_rm04_norm
    (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ r : Real, 0 < r ∧ ∀ x w : E, ‖x‖ < r → ‖w‖ < r →
      ∀ {K R Vb b : Real}, 0 ≤ K → 0 ≤ Vb → b ≤ 1 →
      Real.sqrt (g.inner p x x) ≤ Vb →
      Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          R * Vb ^ 2 ≤ K →
      (∀ t (_ht : t ∈ Ioo (0 : Real) b),
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (radialCurve (I := I) g p x t) 4
          (DifferentialGeometry.Integral.Connection.metricRm04At
            (I := I) (M := M) g (radialCurve (I := I) g p x t))) ≤ R) →
      (g.inner (radialCurve (I := I) g p x 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) s) 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) s) 0)
        ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x 0)
          (radialJacobiField (I := I) g p x w 0)
          (radialJacobiField (I := I) g p x w 0)) →
      ∀ t ∈ Ico (0 : Real) b,
        g.inner (radialCurve (I := I) g p x t)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) s) t)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) s) t)
        ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
          (radialJacobiField (I := I) g p x w t)
          (radialJacobiField (I := I) g p x w t) := by
  obtain ⟨r, hr, hODE⟩ := exists_ode_Ico_of_rm04 (I := I) g p
  refine ⟨r, hr, ?_⟩
  intro x w hx hw K R Vb b hK hVb hb hlaunch hKbound hRm h0
  refine hODE x w hx hw hK hVb hb hlaunch ?_ h0
  intro t ht
  set C : Real := Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real))
    with hC_def
  set A : Real := Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
    (radialCurve (I := I) g p x t) 4
    (DifferentialGeometry.Integral.Connection.metricRm04At
      (I := I) (M := M) g (radialCurve (I := I) g p x t))) with hA_def
  have hCnn : 0 ≤ C := by rw [hC_def]; exact Real.sqrt_nonneg _
  have hVsq : 0 ≤ Vb ^ 2 := sq_nonneg Vb
  have hA_le_R : A ≤ R := by rw [hA_def]; exact hRm t ht
  have hmul : C * A * Vb ^ 2 ≤ C * R * Vb ^ 2 := by
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hA_le_R hCnn) hVsq
  exact le_trans hmul hKbound



omit [SigmaCompactSpace M] in
theorem exists_ode_rm04_d2
    (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ r : Real, 0 < r ∧ ∀ x w : E, ‖x‖ < r → ‖w‖ < r →
      ∀ {K R Vb b : Real}, 0 ≤ K → 0 ≤ Vb → b ≤ 1 →
      Real.sqrt (g.inner p x x) ≤ Vb →
      Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          R * Vb ^ 2 ≤ K →
      (∀ t (_ht : t ∈ Ioo (0 : Real) b),
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (radialCurve (I := I) g p x t) 4
          (DifferentialGeometry.Integral.Connection.metricRm04At
            (I := I) (M := M) g (radialCurve (I := I) g p x t))) ≤ R) →
      covDerivAlong (I := I) g (radialCurve (I := I) g p x)
        (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (radialJacobiField (I := I) g p x w) s) 0 = 0 →
      ∀ t ∈ Ico (0 : Real) b,
        g.inner (radialCurve (I := I) g p x t)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) s) t)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) s) t)
        ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
          (radialJacobiField (I := I) g p x w t)
          (radialJacobiField (I := I) g p x w t) := by
  obtain ⟨r, hr, hODE⟩ := exists_ode_Ico_of_rm04_norm (I := I) g p
  refine ⟨r, hr, ?_⟩
  intro x w hx hw K R Vb b hK hVb hb hlaunch hKbound hRm hD2
  refine hODE x w hx hw hK hVb hb hlaunch hKbound hRm ?_
  rw [hD2, radialJacobi_zero]
  change
    g.inner (radialCurve (I := I) g p x 0)
        (0 : TangentSpace I (radialCurve (I := I) g p x 0))
        (0 : TangentSpace I (radialCurve (I := I) g p x 0)) ≤
      K ^ 2 * g.inner (radialCurve (I := I) g p x 0)
        (0 : TangentSpace I (radialCurve (I := I) g p x 0))
        (0 : TangentSpace I (radialCurve (I := I) g p x 0))
  have hz :
      g.inner (radialCurve (I := I) g p x 0)
        (0 : TangentSpace I (radialCurve (I := I) g p x 0))
        (0 : TangentSpace I (radialCurve (I := I) g p x 0)) = 0 := by
    rw [map_zero]
  rw [hz]
  rw [mul_zero]



omit [SigmaCompactSpace M] in
theorem exists_ode_rm04_jac0
    (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ r : Real, 0 < r ∧ ∀ x w : E, ‖x‖ < r → ‖w‖ < r →
      ∀ {K R Vb b : Real}, 0 ≤ K → 0 ≤ Vb → b ≤ 1 →
      Real.sqrt (g.inner p x x) ≤ Vb →
      Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          R * Vb ^ 2 ≤ K →
      (∀ t (_ht : t ∈ Ioo (0 : Real) b),
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (radialCurve (I := I) g p x t) 4
          (DifferentialGeometry.Integral.Connection.metricRm04At
            (I := I) (M := M) g (radialCurve (I := I) g p x t))) ≤ R) →
      IsJacobiAt (I := I) g (radialCurve (I := I) g p x)
        (radialJacobiField (I := I) g p x w) 0 →
      ∀ t ∈ Ico (0 : Real) b,
        g.inner (radialCurve (I := I) g p x t)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) s) t)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) s) t)
        ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
          (radialJacobiField (I := I) g p x w t)
          (radialJacobiField (I := I) g p x w t) := by
  obtain ⟨r, hr, hODE⟩ := exists_ode_rm04_d2 (I := I) g p
  refine ⟨r, hr, ?_⟩
  intro x w hx hw K R Vb b hK hVb hb hlaunch hKbound hRm hJac0
  exact hODE x w hx hw hK hVb hb hlaunch hKbound hRm
    (d2_zero_of_jac0 (I := I) g p x w hJac0)

open Bundle in
attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in


theorem exists_ode_rm04
    [PseudoEMetricSpace M] [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    ∃ r : Real, 0 < r ∧ ∀ x w : E, ‖x‖ < r → ‖w‖ < r →
      ∀ {K R Vb b : Real}, 0 ≤ K → 0 ≤ Vb → b ≤ 1 →
      Real.sqrt (g.inner p x x) ≤ Vb →
      Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          R * Vb ^ 2 ≤ K →
      (∀ t (_ht : t ∈ Ioo (0 : Real) b),
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (radialCurve (I := I) g p x t) 4
          (DifferentialGeometry.Integral.Connection.metricRm04At
            (I := I) (M := M) g (radialCurve (I := I) g p x t))) ≤ R) →
      ∀ t ∈ Ico (0 : Real) b,
        g.inner (radialCurve (I := I) g p x t)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) s) t)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) s) t)
        ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
          (radialJacobiField (I := I) g p x w t)
          (radialJacobiField (I := I) g p x w t) := by
  obtain ⟨r₀, hr₀, hODE⟩ := exists_ode_rm04_jac0 (I := I) g p
  obtain ⟨r₁, hr₁, hJac0⟩ :=
    exists_radialJacobi_zero_radius (I := I) g hEnorm p
  refine ⟨min r₀ r₁, lt_min hr₀ hr₁, ?_⟩
  intro x w hx hw K R Vb b hK hVb hb hlaunch hKbound hRm
  have hx₀ : ‖x‖ < r₀ := lt_of_lt_of_le hx (min_le_left _ _)
  have hw₀ : ‖w‖ < r₀ := lt_of_lt_of_le hw (min_le_left _ _)
  have hx₁ : ‖x‖ < r₁ := lt_of_lt_of_le hx (min_le_right _ _)
  have hw₁ : ‖w‖ < r₁ := lt_of_lt_of_le hw (min_le_right _ _)
  have hJac0' :
      IsJacobiAt (I := I) g (radialCurve (I := I) g p x)
        (radialJacobiField (I := I) g p x w) 0 := by
    simpa [radialCurve] using hJac0 x w hx₁ hw₁
  exact hODE x w hx₀ hw₀ hK hVb hb hlaunch hKbound hRm hJac0'

open Bundle in
attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in


theorem exists_rm04_data
    [PseudoEMetricSpace M] [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    ∃ r : Real, 0 < r ∧ ∀ x w : E, ‖x‖ < r → ‖w‖ < r →
      ∀ {K R Vb b : Real}, 0 ≤ K → 0 ≤ Vb → b ≤ 1 →
      Real.sqrt (g.inner p x x) ≤ Vb →
      Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          R * Vb ^ 2 ≤ K →
      (∀ t (_ht : t ∈ Ioo (0 : Real) b),
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (radialCurve (I := I) g p x t) 4
          (DifferentialGeometry.Integral.Connection.metricRm04At
            (I := I) (M := M) g (radialCurve (I := I) g p x t))) ≤ R) →
      (∀ t ∈ Icc (0 : ℝ) b,
        DifferentiableAt ℝ
          (chartRepAt (I := I) (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) t) t) ∧
      (∀ t ∈ Icc (0 : ℝ) b,
        DifferentiableAt ℝ
          (chartRepAt (I := I) (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) s) t) t) ∧
      ∀ t ∈ Ico (0 : Real) b,
        g.inner (radialCurve (I := I) g p x t)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) s) t)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) s) t)
        ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
          (radialJacobiField (I := I) g p x w t)
          (radialJacobiField (I := I) g p x w t) := by
  obtain ⟨r₀, hr₀, hdiff⟩ := exists_radialJacobi_diff (I := I) g p
  obtain ⟨r₁, hr₁, hODE⟩ := exists_ode_rm04 (I := I) g hEnorm p
  refine ⟨min r₀ r₁, lt_min hr₀ hr₁, ?_⟩
  intro x w hx hw K R Vb b hK hVb hb hlaunch hKbound hRm
  have hx₀ : ‖x‖ < r₀ := lt_of_lt_of_le hx (min_le_left _ _)
  have hw₀ : ‖w‖ < r₀ := lt_of_lt_of_le hw (min_le_left _ _)
  have hx₁ : ‖x‖ < r₁ := lt_of_lt_of_le hx (min_le_right _ _)
  have hw₁ : ‖w‖ < r₁ := lt_of_lt_of_le hw (min_le_right _ _)
  exact ⟨(hdiff x w hx₀ hw₀ hb).1, (hdiff x w hx₀ hw₀ hb).2,
    hODE x w hx₁ hw₁ hK hVb hb hlaunch hKbound hRm⟩

open Bundle in
attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in

theorem exists_rm04_basis
    [PseudoEMetricSpace M] [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    ∃ r : Real, 0 < r ∧ ∀ x : E, ‖x‖ < r →
      ∀ {a K R Vb b : Real}, 0 ≤ K → 0 ≤ Vb → b ≤ 1 →
      (∀ k : Fin (Module.finrank ℝ E), ‖a • (chartModelBasis E) k‖ < r) →
      Real.sqrt (g.inner p x x) ≤ Vb →
      Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          R * Vb ^ 2 ≤ K →
      (∀ t (_ht : t ∈ Ioo (0 : Real) b),
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (radialCurve (I := I) g p x t) 4
          (DifferentialGeometry.Integral.Connection.metricRm04At
            (I := I) (M := M) g (radialCurve (I := I) g p x t))) ≤ R) →
      (∀ k : Fin (Module.finrank ℝ E), ∀ t ∈ Icc (0 : ℝ) b,
        DifferentiableAt ℝ
          (chartRepAt (I := I) (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x (a • (chartModelBasis E) k)) t) t) ∧
      (∀ k : Fin (Module.finrank ℝ E), ∀ t ∈ Icc (0 : ℝ) b,
        DifferentiableAt ℝ
          (chartRepAt (I := I) (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x (a • (chartModelBasis E) k)) s) t) t) ∧
      ∀ k : Fin (Module.finrank ℝ E), ∀ t ∈ Ico (0 : Real) b,
        g.inner (radialCurve (I := I) g p x t)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x (a • (chartModelBasis E) k)) s) t)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x (a • (chartModelBasis E) k)) s) t)
        ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
          (radialJacobiField (I := I) g p x (a • (chartModelBasis E) k) t)
          (radialJacobiField (I := I) g p x (a • (chartModelBasis E) k) t) := by
  obtain ⟨r, hr, hdata⟩ := exists_rm04_data (I := I) g hEnorm p
  refine ⟨r, hr, ?_⟩
  intro x hx a K R Vb b hK hVb hb hsmall hlaunch hKbound hRm
  refine ⟨?_, ?_, ?_⟩
  · intro k
    exact (hdata x (a • (chartModelBasis E) k) hx (hsmall k)
      hK hVb hb hlaunch hKbound hRm).1
  · intro k
    exact (hdata x (a • (chartModelBasis E) k) hx (hsmall k)
      hK hVb hb hlaunch hKbound hRm).2.1
  · intro k
    exact (hdata x (a • (chartModelBasis E) k) hx (hsmall k)
      hK hVb hb hlaunch hKbound hRm).2.2

open Bundle in
attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in


theorem exists_rm04_pack
    [PseudoEMetricSpace M] [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    ∃ r : Real, 0 < r ∧
      (∀ x : E, ‖x‖ < r →
        ∀ {a K R Vb b : Real}, 0 ≤ K → 0 ≤ Vb → b ≤ 1 →
        (∀ k : Fin (Module.finrank ℝ E), ‖a • (chartModelBasis E) k‖ < r) →
        Real.sqrt (g.inner p x x) ≤ Vb →
        Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
            R * Vb ^ 2 ≤ K →
        (∀ t (_ht : t ∈ Ioo (0 : Real) b),
          Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
            (radialCurve (I := I) g p x t) 4
            (DifferentialGeometry.Integral.Connection.metricRm04At
              (I := I) (M := M) g (radialCurve (I := I) g p x t))) ≤ R) →
        (∀ k : Fin (Module.finrank ℝ E), ∀ t ∈ Icc (0 : ℝ) b,
          DifferentiableAt ℝ
            (chartRepAt (I := I) (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x (a • (chartModelBasis E) k)) t) t) ∧
        (∀ k : Fin (Module.finrank ℝ E), ∀ t ∈ Icc (0 : ℝ) b,
          DifferentiableAt ℝ
            (chartRepAt (I := I) (radialCurve (I := I) g p x)
              (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
                (radialJacobiField (I := I) g p x (a • (chartModelBasis E) k)) s) t) t) ∧
        ∀ k : Fin (Module.finrank ℝ E), ∀ t ∈ Ico (0 : Real) b,
          g.inner (radialCurve (I := I) g p x t)
            (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
                (radialJacobiField (I := I) g p x (a • (chartModelBasis E) k)) s) t)
            (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
                (radialJacobiField (I := I) g p x (a • (chartModelBasis E) k)) s) t)
          ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
            (radialJacobiField (I := I) g p x (a • (chartModelBasis E) k) t)
            (radialJacobiField (I := I) g p x (a • (chartModelBasis E) k) t)) ∧
      (∀ x w : E, ‖x‖ < r → ‖w‖ < r →
        (covDerivAlong (I := I) g
          (fun v : ℝ => (expMap (I := I) g p (show TangentSpace I p from (v • x)) : M))
          (radialJacobiField (I := I) g p x w) 0 : E) = w) := by
  obtain ⟨r₀, hr₀, hdata⟩ := exists_rm04_basis (I := I) g hEnorm p
  obtain ⟨r₁, hr₁, hderiv⟩ := exists_radialJacobi_deriv_radius (I := I) g p
  refine ⟨min r₀ r₁, lt_min hr₀ hr₁, ?_, ?_⟩
  · intro x hx a K R Vb b hK hVb hb hsmall hlaunch hKbound hRm
    have hx₀ : ‖x‖ < r₀ := lt_of_lt_of_le hx (min_le_left _ _)
    refine hdata x hx₀ hK hVb hb ?_ hlaunch hKbound hRm
    intro k
    exact lt_of_lt_of_le (hsmall k) (min_le_left _ _)
  · intro x w hx hw
    have hx₁ : ‖x‖ < r₁ := lt_of_lt_of_le hx (min_le_right _ _)
    have hw₁ : ‖w‖ < r₁ := lt_of_lt_of_le hw (min_le_right _ _)
    exact hderiv x w hx₁ hw₁



omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space (TangentBundle I M)] in
omit [T2Space M] [SigmaCompactSpace M] in
theorem rm04_Ioo_of_region
    (g : SmoothRiemannianMetric I M) (p : M) (x : E)
    {R b : Real} {U : Set M}
    (hcurve : ∀ t : Real, t ∈ Ioo (0 : Real) b →
      radialCurve (I := I) g p x t ∈ U)
    (hRmU : ∀ q : M, q ∈ U →
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g q 4
        (DifferentialGeometry.Integral.Connection.metricRm04At
          (I := I) (M := M) g q)) ≤ R) :
    ∀ t (_ht : t ∈ Ioo (0 : Real) b),
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
        (radialCurve (I := I) g p x t) 4
        (DifferentialGeometry.Integral.Connection.metricRm04At
          (I := I) (M := M) g (radialCurve (I := I) g p x t))) ≤ R := by
  intro t ht
  exact hRmU _ (hcurve t ht)

open Bundle in
attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in



theorem exists_ode_rm04_on
    [PseudoEMetricSpace M] [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M) (p : M) :
    (∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))) →
    ∃ r : Real, 0 < r ∧ ∀ x w : E, ‖x‖ < r → ‖w‖ < r →
      ∀ {K R Vb b : Real} {U : Set M}, 0 ≤ K → 0 ≤ Vb → b ≤ 1 →
      Real.sqrt (g.inner p x x) ≤ Vb →
      Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          R * Vb ^ 2 ≤ K →
      (∀ t : Real, t ∈ Ioo (0 : Real) b →
        radialCurve (I := I) g p x t ∈ U) →
      (∀ q : M, q ∈ U →
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g q 4
          (DifferentialGeometry.Integral.Connection.metricRm04At
            (I := I) (M := M) g q)) ≤ R) →
      ∀ t ∈ Ico (0 : Real) b,
        g.inner (radialCurve (I := I) g p x t)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) s) t)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) s) t)
        ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
          (radialJacobiField (I := I) g p x w t)
          (radialJacobiField (I := I) g p x w t) := by
  intro hEnorm
  obtain ⟨r, hr, hODE⟩ := exists_ode_rm04 (I := I) g hEnorm p
  refine ⟨r, hr, ?_⟩
  intro x w hx hw K R Vb b U hK hVb hb hlaunch hKbound hcurve hRmU
  exact hODE x w hx hw hK hVb hb hlaunch hKbound
    (rm04_Ioo_of_region (I := I) g p x hcurve hRmU)



omit [SigmaCompactSpace M] in
theorem exists_ode_expBall
    (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ r : Real, 0 < r ∧ ∀ x w : E, ‖x‖ < r → ‖w‖ < r →
      ∀ {K R Vb b ρ : Real}, 0 ≤ K → 0 ≤ Vb → b ≤ 1 → ‖x‖ < ρ →
      Real.sqrt (g.inner p x x) ≤ Vb →
      Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          R * Vb ^ 2 ≤ K →
      (∀ q : M, q ∈
        (fun v : TangentSpace I p => expMap (I := I) g p v) ''
          {v : TangentSpace I p | ‖v‖ < ρ} →
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g q 4
          (DifferentialGeometry.Integral.Connection.metricRm04At
            (I := I) (M := M) g q)) ≤ R) →
      IsJacobiAt (I := I) g (radialCurve (I := I) g p x)
        (radialJacobiField (I := I) g p x w) 0 →
      ∀ t ∈ Ico (0 : Real) b,
        g.inner (radialCurve (I := I) g p x t)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) s) t)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) s) t)
        ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
          (radialJacobiField (I := I) g p x w t)
          (radialJacobiField (I := I) g p x w t) := by
  obtain ⟨r, hr, hODE⟩ := exists_ode_rm04_jac0 (I := I) g p
  refine ⟨r, hr, ?_⟩
  intro x w hx hw K R Vb b ρ hK hVb hb hxρ hlaunch hKbound hRm hJac0
  exact hODE x w hx hw hK hVb hb hlaunch hKbound
    (rm04_Ioo_of_region (I := I) g p x
      (radial_mem_expBall (I := I) g p x hxρ hb) hRm) hJac0



omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space (TangentBundle I M)] in
omit [T2Space M] [SigmaCompactSpace M] in
theorem rm04Exp_of_global
    (g : SmoothRiemannianMetric I M) (p : M) {R ρ : Real}
    (hRm : ∀ q : M,
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g q 4
        (DifferentialGeometry.Integral.Connection.metricRm04At
          (I := I) (M := M) g q)) ≤ R) :
    ∀ q : M, q ∈
      (fun v : TangentSpace I p => expMap (I := I) g p v) ''
        {v : TangentSpace I p | ‖v‖ < ρ} →
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g q 4
        (DifferentialGeometry.Integral.Connection.metricRm04At
          (I := I) (M := M) g q)) ≤ R := by
  intro q _hq
  exact hRm q




omit [SigmaCompactSpace M] in
theorem exists_ode_global
    (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ r : Real, 0 < r ∧ ∀ x w : E, ‖x‖ < r → ‖w‖ < r →
      ∀ {K R Vb b ρ : Real}, 0 ≤ K → 0 ≤ Vb → b ≤ 1 → ‖x‖ < ρ →
      Real.sqrt (g.inner p x x) ≤ Vb →
      Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          R * Vb ^ 2 ≤ K →
      (∀ q : M,
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g q 4
          (DifferentialGeometry.Integral.Connection.metricRm04At
            (I := I) (M := M) g q)) ≤ R) →
      IsJacobiAt (I := I) g (radialCurve (I := I) g p x)
        (radialJacobiField (I := I) g p x w) 0 →
      ∀ t ∈ Ico (0 : Real) b,
        g.inner (radialCurve (I := I) g p x t)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) s) t)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) s) t)
        ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
          (radialJacobiField (I := I) g p x w t)
          (radialJacobiField (I := I) g p x w t) := by
  obtain ⟨r, hr, hODE⟩ := exists_ode_expBall (I := I) g p
  refine ⟨r, hr, ?_⟩
  intro x w hx hw K R Vb b ρ hK hVb hb hxρ hlaunch hKbound hRm hJac0
  exact hODE x w hx hw hK hVb hb hxρ hlaunch hKbound
    (rm04Exp_of_global (I := I) g p hRm) hJac0


private noncomputable def coeffModelCLM :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) →L[ℝ] E :=
  (toEuclidean (E := E)).symm.toContinuousLinearMap

omit [NeZero (Module.finrank ℝ E)] in
private lemma coeffModelCLM_eq_sum
    (v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    coeffModelCLM (E := E) v = ∑ i, v i • (chartModelBasis E) i := by
  have hvsum : v = ∑ i, v i • EuclideanSpace.single i (1 : ℝ) := by
    let b := (EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ).toBasis
    simpa [b, EuclideanSpace.basisFun_apply] using (b.sum_repr v).symm
  calc
    coeffModelCLM (E := E) v =
        (toEuclidean (E := E)).symm v := rfl
    _ = (toEuclidean (E := E)).symm (∑ i, v i • EuclideanSpace.single i (1 : ℝ)) := by
          exact congrArg (toEuclidean (E := E)).symm hvsum
    _ = ∑ i, v i • (toEuclidean (E := E)).symm (EuclideanSpace.single i (1 : ℝ)) := by
          rw [map_sum]
          simp only [map_smul]
    _ = ∑ i, v i • (chartModelBasis E) i := by
          simp only [chartModelBasis_apply]

omit [T2Space M] [SigmaCompactSpace M] in
omit [I.Boundaryless] [T2Space (TangentBundle I M)] in
private lemma sqrt_coercive_mul_norm_le
    (g : SmoothRiemannianMetric I M) (p : M)
    (x : E) :
    Real.sqrt (gpCoerciveConst (I := I) g p) * ‖x‖ ≤
      Real.sqrt (g.inner p x x) := by
  have hc_pos : 0 < gpCoerciveConst (I := I) g p := gpCoerciveConst_pos (I := I) g p
  have hcoerc : gpCoerciveConst (I := I) g p * ‖x‖ ^ 2 ≤ g.inner p x x :=
    gpCoerciveConst_le (I := I) g p x
  have hlhs_eq : Real.sqrt (gpCoerciveConst (I := I) g p) * ‖x‖ =
      Real.sqrt (gpCoerciveConst (I := I) g p * ‖x‖ ^ 2) := by
    rw [Real.sqrt_mul hc_pos.le, Real.sqrt_sq (norm_nonneg x)]
  rw [hlhs_eq]
  exact Real.sqrt_le_sqrt hcoerc

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
private lemma inner_le_opNorm_sq
    (g : SmoothRiemannianMetric I M) (p : M)
    (x : E) :
    g.inner p x x ≤ ‖g.inner p‖ * ‖x‖ ^ 2 := by
  have hlin : ‖(g.inner p) x‖ ≤ ‖g.inner p‖ * ‖x‖ :=
    (g.inner p).le_opNorm x
  have happ : ‖((g.inner p) x) x‖ ≤ ‖(g.inner p) x‖ * ‖x‖ :=
    ((g.inner p) x).le_opNorm x
  have hmul :
      ‖((g.inner p) x) x‖ ≤ (‖g.inner p‖ * ‖x‖) * ‖x‖ :=
    happ.trans (mul_le_mul_of_nonneg_right hlin (norm_nonneg x))
  have hself : g.inner p x x ≤ ‖((g.inner p) x) x‖ := by
    exact Real.le_norm_self _
  calc
    g.inner p x x ≤ ‖((g.inner p) x) x‖ := hself
    _ ≤ (‖g.inner p‖ * ‖x‖) * ‖x‖ := hmul
    _ = ‖g.inner p‖ * ‖x‖ ^ 2 := by ring





omit [T2Space M] [SigmaCompactSpace M] in
omit [I.Boundaryless] [T2Space (TangentBundle I M)] in
theorem exists_unitCoeff_ge
    (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ B : ℝ, 0 < B ∧
      ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
        B ≤ Real.sqrt
          (g.inner p (∑ i, v i • (chartModelBasis E) i)
            (∑ i, v i • (chartModelBasis E) i)) := by
  let L : E →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
    (toEuclidean (E := E)).toContinuousLinearMap
  let K : ℝ := ‖L‖ + 1
  let B : ℝ := Real.sqrt (gpCoerciveConst (I := I) g p) / K
  have hc_pos : 0 < Real.sqrt (gpCoerciveConst (I := I) g p) :=
    Real.sqrt_pos.mpr (gpCoerciveConst_pos (I := I) g p)
  have hden_pos : 0 < K := by
    have hL_nonneg : 0 ≤ ‖L‖ := norm_nonneg L
    linarith
  refine ⟨B, div_pos hc_pos hden_pos, ?_⟩
  intro v hv
  have hanti :=
    (ContinuousLinearEquiv.antilipschitz ((toEuclidean (E := E)).symm)).le_mul_dist v 0
  have hunit_le :
      1 ≤ K * ‖coeffModelCLM (E := E) v‖ := by
    simp only [map_zero, dist_zero_right] at hanti
    rw [hv] at hanti
    have hK0_le : (↑‖L‖₊ : ℝ) ≤ K := by
      simp [K, L]
    have hanti' : 1 ≤ (↑‖L‖₊ : ℝ) * ‖coeffModelCLM (E := E) v‖ := by
      simpa [L, coeffModelCLM] using hanti
    exact hanti'.trans
      (mul_le_mul_of_nonneg_right hK0_le (norm_nonneg _))
  have hnorm_lower : 1 / K ≤ ‖coeffModelCLM (E := E) v‖ := by
    exact (div_le_iff₀ hden_pos).2 (by rwa [mul_comm])
  have hmetric := sqrt_coercive_mul_norm_le (I := I) g p (coeffModelCLM (E := E) v)
  have hB_le :
      B ≤ Real.sqrt (gpCoerciveConst (I := I) g p) * ‖coeffModelCLM (E := E) v‖ := by
    dsimp [B]
    rw [div_eq_mul_inv]
    have hnorm_inv : K⁻¹ ≤ ‖coeffModelCLM (E := E) v‖ := by
      simpa [one_div] using hnorm_lower
    exact mul_le_mul_of_nonneg_left hnorm_inv hc_pos.le
  calc
    B ≤ Real.sqrt (gpCoerciveConst (I := I) g p) * ‖coeffModelCLM (E := E) v‖ := hB_le
    _ ≤ Real.sqrt (g.inner p (coeffModelCLM (E := E) v) (coeffModelCLM (E := E) v)) :=
        hmetric
    _ = Real.sqrt
          (g.inner p (∑ i, v i • (chartModelBasis E) i)
            (∑ i, v i • (chartModelBasis E) i)) := by
        rw [coeffModelCLM_eq_sum (E := E) v]
        rfl


omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
theorem exists_unitCoeff_le
    (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ D : ℝ, 0 ≤ D ∧
      ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
        Real.sqrt
          (g.inner p (∑ i, v i • (chartModelBasis E) i)
            (∑ i, v i • (chartModelBasis E) i)) ≤ D := by
  let C : ℝ := ‖coeffModelCLM (E := E)‖
  let D : ℝ := Real.sqrt (‖g.inner p‖ * C ^ 2)
  refine ⟨D, Real.sqrt_nonneg _, ?_⟩
  intro v hv
  have hdir_le : ‖coeffModelCLM (E := E) v‖ ≤ C := by
    have hop := (coeffModelCLM (E := E)).le_opNorm v
    simpa [C, hv] using hop
  have hsq_le : ‖coeffModelCLM (E := E) v‖ ^ 2 ≤ C ^ 2 := by
    have hC_nonneg : 0 ≤ C := by
      exact norm_nonneg (coeffModelCLM (E := E))
    exact (sq_le_sq₀ (norm_nonneg _) hC_nonneg).2 hdir_le
  have hinner_le :
      g.inner p (coeffModelCLM (E := E) v) (coeffModelCLM (E := E) v) ≤
        ‖g.inner p‖ * C ^ 2 := by
    exact (inner_le_opNorm_sq (I := I) g p (coeffModelCLM (E := E) v)).trans
      (mul_le_mul_of_nonneg_left hsq_le (norm_nonneg (g.inner p)))
  calc
    Real.sqrt
          (g.inner p (∑ i, v i • (chartModelBasis E) i)
            (∑ i, v i • (chartModelBasis E) i))
        = Real.sqrt (g.inner p (coeffModelCLM (E := E) v) (coeffModelCLM (E := E) v)) := by
          rw [coeffModelCLM_eq_sum (E := E) v]
          rfl
    _ ≤ D := Real.sqrt_le_sqrt hinner_le



omit [T2Space M] [SigmaCompactSpace M] in
omit [I.Boundaryless] [T2Space (TangentBundle I M)] in
theorem exists_unitCoeff_bounds
    (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ B₀ D : ℝ, 0 < B₀ ∧ 0 ≤ D ∧
      (∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
        B₀ ≤ Real.sqrt
          (g.inner p (∑ i, v i • (chartModelBasis E) i)
            (∑ i, v i • (chartModelBasis E) i))) ∧
      (∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
        Real.sqrt
          (g.inner p (∑ i, v i • (chartModelBasis E) i)
            (∑ i, v i • (chartModelBasis E) i)) ≤ D) := by
  rcases exists_unitCoeff_ge (I := I) g p with ⟨B₀, hB₀_pos, hB₀⟩
  rcases exists_unitCoeff_le (I := I) g p with ⟨D, hD_nonneg, hD⟩
  exact ⟨B₀, D, hB₀_pos, hD_nonneg, hB₀, hD⟩



omit [NeZero (Module.finrank ℝ E)] in
lemma unitDirScaleSmall {r : ℝ} (hr : 0 < r) :
    ∃ a : ℝ, 0 < a ∧
      ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
        ‖a • (∑ i, v i • (chartModelBasis E) i)‖ < r := by
  set C : ℝ := ‖coeffModelCLM (E := E)‖ with hC
  have hC_nonneg : 0 ≤ C := by
    simp [hC]
  have hden_pos : 0 < C + 1 := by linarith
  refine ⟨r / (C + 1), div_pos hr hden_pos, ?_⟩
  intro v hv
  have ha_pos : 0 < r / (C + 1) := div_pos hr hden_pos
  have hdir_le : ‖∑ i, v i • (chartModelBasis E) i‖ ≤ C := by
    have hop := (coeffModelCLM (E := E)).le_opNorm v
    rw [hv, mul_one] at hop
    rw [← coeffModelCLM_eq_sum (E := E) v]
    simpa [hC] using hop
  have hdir_lt : ‖∑ i, v i • (chartModelBasis E) i‖ < C + 1 := by
    linarith
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha_pos]
  calc
    r / (C + 1) * ‖∑ i, v i • (chartModelBasis E) i‖
        < r / (C + 1) * (C + 1) :=
          mul_lt_mul_of_pos_left hdir_lt ha_pos
    _ = r := by field_simp [ne_of_gt hden_pos]







omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
lemma dir_deriv_radius
    (g : SmoothRiemannianMetric I M) (p : M) {r : ℝ} (x : E)
    (hderivRadius : ∀ x w : E, ‖x‖ < r → ‖w‖ < r →
      (covDerivAlong (I := I) g
        (fun v : ℝ => (expMap (I := I) g p (show TangentSpace I p from (v • x)) : M))
        (radialJacobiField (I := I) g p x w) 0 : E) = w)
    (hx : ‖x‖ < r)
    (hdirSmall : ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
      ‖∑ i, v i • (chartModelBasis E) i‖ < r) :
    ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
      (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
        (radialJacobiField (I := I) g p x
          (∑ i, v i • (chartModelBasis E) i)) 0 : E) =
        ∑ i, v i • (chartModelBasis E) i := by
  intro v hv
  simpa [radialCurve] using
    hderivRadius x (∑ i, v i • (chartModelBasis E) i) hx (hdirSmall v hv)




omit [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma dir_init_ge
    (g : SmoothRiemannianMetric I M) (p : M) (x : E) {B : ℝ}
    (hB : ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
      B ≤ Real.sqrt
        (g.inner p (∑ i, v i • (chartModelBasis E) i)
          (∑ i, v i • (chartModelBasis E) i)))
    (hderiv : ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
      (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
        (radialJacobiField (I := I) g p x
          (∑ i, v i • (chartModelBasis E) i)) 0 : E) =
        ∑ i, v i • (chartModelBasis E) i) :
    ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
      B ≤ Real.sqrt
        (g.inner (radialCurve (I := I) g p x 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x
              (∑ i, v i • (chartModelBasis E) i)) 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x
              (∑ i, v i • (chartModelBasis E) i)) 0)) := by
  intro v hv
  rw [radialCurve_zero (I := I) g p x]
  rw [hderiv v hv]
  exact hB v hv





omit [T2Space M] [SigmaCompactSpace M] in
theorem exists_dirInit_ge
    (g : SmoothRiemannianMetric I M) (p : M) (x : E)
    (hderiv : ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
      (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
        (radialJacobiField (I := I) g p x
          (∑ i, v i • (chartModelBasis E) i)) 0 : E) =
        ∑ i, v i • (chartModelBasis E) i) :
    ∃ B : ℝ, 0 < B ∧
      ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
        B ≤ Real.sqrt
          (g.inner (radialCurve (I := I) g p x 0)
            (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x
                (∑ i, v i • (chartModelBasis E) i)) 0)
            (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x
                (∑ i, v i • (chartModelBasis E) i)) 0)) := by
  rcases exists_unitCoeff_ge (I := I) g p with ⟨B, hBpos, hB⟩
  exact ⟨B, hBpos, dir_init_ge (I := I) g p x hB hderiv⟩










omit [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem radialJacobi_bounds_at
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E)
    {K b : ℝ} (hK : 0 ≤ K) (hb : 0 ≤ b)
    (hγ : ∀ t ∈ Icc (0 : ℝ) b,
      ContMDiffAt 𝓘(ℝ, ℝ) I 1 (radialCurve (I := I) g p x) t)
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (hcard : ∀ t : ℝ,
      Fintype.card ι = Module.finrank ℝ (TangentSpace I (radialCurve (I := I) g p x t)))
    (F : ι → ∀ t : ℝ, TangentSpace I (radialCurve (I := I) g p x t))
    (hpar : ∀ i, ∀ t ∈ Icc (0 : ℝ) b,
      covDerivAlong (I := I) g (radialCurve (I := I) g p x) (F i) t = 0)
    (hON : ∀ t ∈ Icc (0 : ℝ) b, ∀ i j,
      g.inner (radialCurve (I := I) g p x t) (F i t) (F j t) =
        if i = j then (1 : ℝ) else 0)
    (hFdiff : ∀ i, ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x) (F i) t) t)
    (hJdiff : ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x)
          (radialJacobiField (I := I) g p x w) t) t)
    (hDJdiff : ∀ t ∈ Icc (0 : ℝ) b, DifferentiableAt ℝ
      (chartRepAt (I := I) (radialCurve (I := I) g p x)
        (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (radialJacobiField (I := I) g p x w) s) t) t)
    (hODE : ∀ t ∈ Ico (0 : ℝ) b,
      g.inner (radialCurve (I := I) g p x t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) s) t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) s) t)
      ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
        (radialJacobiField (I := I) g p x w t)
        (radialJacobiField (I := I) g p x w t)) :
    (∀ t ∈ Icc (0 : ℝ) b,
      Real.sqrt (g.inner (radialCurve (I := I) g p x t)
        (radialJacobiField (I := I) g p x w t)
        (radialJacobiField (I := I) g p x w t)) ≤
        t * Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) 0)) +
          gronwallBound 0 (max K 1)
            (K * (b * Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
              (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
                (radialJacobiField (I := I) g p x w) 0)
              (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
                (radialJacobiField (I := I) g p x w) 0)))) t) ∧
    (∀ t ∈ Icc (0 : ℝ) b,
      t * Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) 0)) -
          gronwallBound 0 (max K 1)
            (K * (b * Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
              (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
                (radialJacobiField (I := I) g p x w) 0)
              (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
                (radialJacobiField (I := I) g p x w) 0)))) t ≤
        Real.sqrt (g.inner (radialCurve (I := I) g p x t)
          (radialJacobiField (I := I) g p x w t)
          (radialJacobiField (I := I) g p x w t))) := by
  simpa [radialCurve] using
    covGronwall_bounds_at (I := I) g (radialCurve (I := I) g p x) hγ hcard F
      (radialJacobiField (I := I) g p x w) hK hb hpar hON hFdiff hJdiff
      hDJdiff hODE (radialJacobi_zero (I := I) g p x w) rfl



omit [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem radialJacobi_bounds
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E)
    {K b : ℝ} (hK : 0 ≤ K) (hb : 0 ≤ b)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 (radialCurve (I := I) g p x))
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (hcard : ∀ t : ℝ,
      Fintype.card ι = Module.finrank ℝ (TangentSpace I (radialCurve (I := I) g p x t)))
    (F : ι → ∀ t : ℝ, TangentSpace I (radialCurve (I := I) g p x t))
    (hpar : ∀ i, ∀ t ∈ Icc (0 : ℝ) b,
      covDerivAlong (I := I) g (radialCurve (I := I) g p x) (F i) t = 0)
    (hON : ∀ t ∈ Icc (0 : ℝ) b, ∀ i j,
      g.inner (radialCurve (I := I) g p x t) (F i t) (F j t) =
        if i = j then (1 : ℝ) else 0)
    (hFdiff : ∀ i, ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x) (F i) t) t)
    (hJdiff : ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x)
          (radialJacobiField (I := I) g p x w) t) t)
    (hDJdiff : ∀ t ∈ Icc (0 : ℝ) b, DifferentiableAt ℝ
      (chartRepAt (I := I) (radialCurve (I := I) g p x)
        (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (radialJacobiField (I := I) g p x w) s) t) t)
    (hODE : ∀ t ∈ Ico (0 : ℝ) b,
      g.inner (radialCurve (I := I) g p x t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) s) t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) s) t)
      ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
        (radialJacobiField (I := I) g p x w t)
        (radialJacobiField (I := I) g p x w t)) :
    (∀ t ∈ Icc (0 : ℝ) b,
      Real.sqrt (g.inner (radialCurve (I := I) g p x t)
        (radialJacobiField (I := I) g p x w t)
        (radialJacobiField (I := I) g p x w t)) ≤
        t * Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) 0)) +
          gronwallBound 0 (max K 1)
            (K * (b * Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
              (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
                (radialJacobiField (I := I) g p x w) 0)
              (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
                (radialJacobiField (I := I) g p x w) 0)))) t) ∧
    (∀ t ∈ Icc (0 : ℝ) b,
      t * Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) 0)) -
          gronwallBound 0 (max K 1)
            (K * (b * Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
              (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
                (radialJacobiField (I := I) g p x w) 0)
              (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
                (radialJacobiField (I := I) g p x w) 0)))) t ≤
        Real.sqrt (g.inner (radialCurve (I := I) g p x t)
          (radialJacobiField (I := I) g p x w t)
          (radialJacobiField (I := I) g p x w t))) := by
  refine radialJacobi_bounds_at (I := I) g p x w hK hb (fun t _ => ?_) hcard F
    hpar hON hFdiff hJdiff hDJdiff hODE
  exact hγ.contMDiffAt






omit [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem radialJacobi_one_bounds_at
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E)
    {K b : ℝ} (hK : 0 ≤ K) (hb : 0 ≤ b) (h1b : (1 : ℝ) ≤ b)
    (hγ : ∀ t ∈ Icc (0 : ℝ) b,
      ContMDiffAt 𝓘(ℝ, ℝ) I 1 (radialCurve (I := I) g p x) t)
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (hcard : ∀ t : ℝ,
      Fintype.card ι = Module.finrank ℝ (TangentSpace I (radialCurve (I := I) g p x t)))
    (F : ι → ∀ t : ℝ, TangentSpace I (radialCurve (I := I) g p x t))
    (hpar : ∀ i, ∀ t ∈ Icc (0 : ℝ) b,
      covDerivAlong (I := I) g (radialCurve (I := I) g p x) (F i) t = 0)
    (hON : ∀ t ∈ Icc (0 : ℝ) b, ∀ i j,
      g.inner (radialCurve (I := I) g p x t) (F i t) (F j t) =
        if i = j then (1 : ℝ) else 0)
    (hFdiff : ∀ i, ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x) (F i) t) t)
    (hJdiff : ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x)
          (radialJacobiField (I := I) g p x w) t) t)
    (hDJdiff : ∀ t ∈ Icc (0 : ℝ) b, DifferentiableAt ℝ
      (chartRepAt (I := I) (radialCurve (I := I) g p x)
        (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (radialJacobiField (I := I) g p x w) s) t) t)
    (hODE : ∀ t ∈ Ico (0 : ℝ) b,
      g.inner (radialCurve (I := I) g p x t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) s) t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) s) t)
      ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
        (radialJacobiField (I := I) g p x w t)
        (radialJacobiField (I := I) g p x w t)) :
    (Real.sqrt (g.inner (radialCurve (I := I) g p x 1)
      (radialJacobiField (I := I) g p x w 1)
      (radialJacobiField (I := I) g p x w 1)) ≤
        Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) 0)) +
          gronwallBound 0 (max K 1)
            (K * (b * Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
              (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
                (radialJacobiField (I := I) g p x w) 0)
              (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
                (radialJacobiField (I := I) g p x w) 0)))) 1) ∧
    (Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) 0)) -
          gronwallBound 0 (max K 1)
            (K * (b * Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
              (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
                (radialJacobiField (I := I) g p x w) 0)
              (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
                (radialJacobiField (I := I) g p x w) 0)))) 1 ≤
        Real.sqrt (g.inner (radialCurve (I := I) g p x 1)
          (radialJacobiField (I := I) g p x w 1)
          (radialJacobiField (I := I) g p x w 1))) := by
  have hbounds := radialJacobi_bounds_at (I := I) g p x w hK hb hγ hcard F hpar hON
    hFdiff hJdiff hDJdiff hODE
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) b := ⟨by norm_num, h1b⟩
  constructor
  · simpa using hbounds.1 1 h1
  · simpa using hbounds.2 1 h1



omit [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem radialJacobi_one_bounds
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E)
    {K b : ℝ} (hK : 0 ≤ K) (hb : 0 ≤ b) (h1b : (1 : ℝ) ≤ b)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 (radialCurve (I := I) g p x))
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (hcard : ∀ t : ℝ,
      Fintype.card ι = Module.finrank ℝ (TangentSpace I (radialCurve (I := I) g p x t)))
    (F : ι → ∀ t : ℝ, TangentSpace I (radialCurve (I := I) g p x t))
    (hpar : ∀ i, ∀ t ∈ Icc (0 : ℝ) b,
      covDerivAlong (I := I) g (radialCurve (I := I) g p x) (F i) t = 0)
    (hON : ∀ t ∈ Icc (0 : ℝ) b, ∀ i j,
      g.inner (radialCurve (I := I) g p x t) (F i t) (F j t) =
        if i = j then (1 : ℝ) else 0)
    (hFdiff : ∀ i, ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x) (F i) t) t)
    (hJdiff : ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x)
          (radialJacobiField (I := I) g p x w) t) t)
    (hDJdiff : ∀ t ∈ Icc (0 : ℝ) b, DifferentiableAt ℝ
      (chartRepAt (I := I) (radialCurve (I := I) g p x)
        (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (radialJacobiField (I := I) g p x w) s) t) t)
    (hODE : ∀ t ∈ Ico (0 : ℝ) b,
      g.inner (radialCurve (I := I) g p x t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) s) t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) s) t)
      ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
        (radialJacobiField (I := I) g p x w t)
        (radialJacobiField (I := I) g p x w t)) :
    (Real.sqrt (g.inner (radialCurve (I := I) g p x 1)
      (radialJacobiField (I := I) g p x w 1)
      (radialJacobiField (I := I) g p x w 1)) ≤
        Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) 0)) +
          gronwallBound 0 (max K 1)
            (K * (b * Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
              (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
                (radialJacobiField (I := I) g p x w) 0)
              (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
                (radialJacobiField (I := I) g p x w) 0)))) 1) ∧
    (Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) 0)) -
          gronwallBound 0 (max K 1)
            (K * (b * Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
              (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
                (radialJacobiField (I := I) g p x w) 0)
              (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
                (radialJacobiField (I := I) g p x w) 0)))) 1 ≤
        Real.sqrt (g.inner (radialCurve (I := I) g p x 1)
          (radialJacobiField (I := I) g p x w 1)
          (radialJacobiField (I := I) g p x w 1))) := by
  refine radialJacobi_one_bounds_at (I := I) g p x w hK hb h1b
    (fun t _ => ?_) hcard F hpar hON hFdiff hJdiff hDJdiff hODE
  exact hγ.contMDiffAt


omit [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem radialJacobi_one_le_at
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E)
    {K b B : ℝ} (hK : 0 ≤ K) (hb : 0 ≤ b) (h1b : (1 : ℝ) ≤ b)
    (hγ : ∀ t ∈ Icc (0 : ℝ) b,
      ContMDiffAt 𝓘(ℝ, ℝ) I 1 (radialCurve (I := I) g p x) t)
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (hcard : ∀ t : ℝ,
      Fintype.card ι = Module.finrank ℝ (TangentSpace I (radialCurve (I := I) g p x t)))
    (F : ι → ∀ t : ℝ, TangentSpace I (radialCurve (I := I) g p x t))
    (hpar : ∀ i, ∀ t ∈ Icc (0 : ℝ) b,
      covDerivAlong (I := I) g (radialCurve (I := I) g p x) (F i) t = 0)
    (hON : ∀ t ∈ Icc (0 : ℝ) b, ∀ i j,
      g.inner (radialCurve (I := I) g p x t) (F i t) (F j t) =
        if i = j then (1 : ℝ) else 0)
    (hFdiff : ∀ i, ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x) (F i) t) t)
    (hJdiff : ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x)
          (radialJacobiField (I := I) g p x w) t) t)
    (hDJdiff : ∀ t ∈ Icc (0 : ℝ) b, DifferentiableAt ℝ
      (chartRepAt (I := I) (radialCurve (I := I) g p x)
        (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (radialJacobiField (I := I) g p x w) s) t) t)
    (hODE : ∀ t ∈ Ico (0 : ℝ) b,
      g.inner (radialCurve (I := I) g p x t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) s) t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) s) t)
      ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
        (radialJacobiField (I := I) g p x w t)
        (radialJacobiField (I := I) g p x w t))
    (hB :
      Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) 0)) +
          gronwallBound 0 (max K 1)
            (K * (b * Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
              (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
                (radialJacobiField (I := I) g p x w) 0)
              (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
                (radialJacobiField (I := I) g p x w) 0)))) 1 ≤ B) :
    Real.sqrt (g.inner (expMap (I := I) g p (show TangentSpace I p from x))
      (radialJacobiField (I := I) g p x w 1)
      (radialJacobiField (I := I) g p x w 1)) ≤ B := by
  have hbounds := radialJacobi_one_bounds_at (I := I) g p x w hK hb h1b hγ hcard F
    hpar hON hFdiff hJdiff hDJdiff hODE
  have hupper :
      Real.sqrt (g.inner (expMap (I := I) g p (show TangentSpace I p from x))
        (radialJacobiField (I := I) g p x w 1)
        (radialJacobiField (I := I) g p x w 1)) ≤
          Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
            (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) 0)
            (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) 0)) +
            gronwallBound 0 (max K 1)
              (K * (b * Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
                (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
                  (radialJacobiField (I := I) g p x w) 0)
                (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
                  (radialJacobiField (I := I) g p x w) 0)))) 1 := by
    rw [← radialCurve_one (I := I) g p x]
    exact hbounds.1
  exact hupper.trans hB






omit [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem radialJacobi_one_le
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E)
    {K b B : ℝ} (hK : 0 ≤ K) (hb : 0 ≤ b) (h1b : (1 : ℝ) ≤ b)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 (radialCurve (I := I) g p x))
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (hcard : ∀ t : ℝ,
      Fintype.card ι = Module.finrank ℝ (TangentSpace I (radialCurve (I := I) g p x t)))
    (F : ι → ∀ t : ℝ, TangentSpace I (radialCurve (I := I) g p x t))
    (hpar : ∀ i, ∀ t ∈ Icc (0 : ℝ) b,
      covDerivAlong (I := I) g (radialCurve (I := I) g p x) (F i) t = 0)
    (hON : ∀ t ∈ Icc (0 : ℝ) b, ∀ i j,
      g.inner (radialCurve (I := I) g p x t) (F i t) (F j t) =
        if i = j then (1 : ℝ) else 0)
    (hFdiff : ∀ i, ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x) (F i) t) t)
    (hJdiff : ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x)
          (radialJacobiField (I := I) g p x w) t) t)
    (hDJdiff : ∀ t ∈ Icc (0 : ℝ) b, DifferentiableAt ℝ
      (chartRepAt (I := I) (radialCurve (I := I) g p x)
        (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (radialJacobiField (I := I) g p x w) s) t) t)
    (hODE : ∀ t ∈ Ico (0 : ℝ) b,
      g.inner (radialCurve (I := I) g p x t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) s) t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) s) t)
      ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
        (radialJacobiField (I := I) g p x w t)
        (radialJacobiField (I := I) g p x w t))
    (hB :
      Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) 0)) +
          gronwallBound 0 (max K 1)
            (K * (b * Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
              (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
                (radialJacobiField (I := I) g p x w) 0)
              (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
                (radialJacobiField (I := I) g p x w) 0)))) 1 ≤ B) :
    Real.sqrt (g.inner (expMap (I := I) g p (show TangentSpace I p from x))
      (radialJacobiField (I := I) g p x w 1)
      (radialJacobiField (I := I) g p x w 1)) ≤ B := by
  have hbounds := radialJacobi_one_bounds (I := I) g p x w hK hb h1b hγ hcard F
    hpar hON hFdiff hJdiff hDJdiff hODE
  have hupper :
      Real.sqrt (g.inner (expMap (I := I) g p (show TangentSpace I p from x))
        (radialJacobiField (I := I) g p x w 1)
        (radialJacobiField (I := I) g p x w 1)) ≤
          Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
            (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) 0)
            (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x w) 0)) +
            gronwallBound 0 (max K 1)
              (K * (b * Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
                (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
                  (radialJacobiField (I := I) g p x w) 0)
                (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
                  (radialJacobiField (I := I) g p x w) 0)))) 1 := by
    rw [← radialCurve_one (I := I) g p x]
    exact hbounds.1
  exact hupper.trans hB


omit [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem radialJacobi_one_ge_at
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E)
    {K b B : ℝ} (hK : 0 ≤ K) (hb : 0 ≤ b) (h1b : (1 : ℝ) ≤ b)
    (hγ : ∀ t ∈ Icc (0 : ℝ) b,
      ContMDiffAt 𝓘(ℝ, ℝ) I 1 (radialCurve (I := I) g p x) t)
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (hcard : ∀ t : ℝ,
      Fintype.card ι = Module.finrank ℝ (TangentSpace I (radialCurve (I := I) g p x t)))
    (F : ι → ∀ t : ℝ, TangentSpace I (radialCurve (I := I) g p x t))
    (hpar : ∀ i, ∀ t ∈ Icc (0 : ℝ) b,
      covDerivAlong (I := I) g (radialCurve (I := I) g p x) (F i) t = 0)
    (hON : ∀ t ∈ Icc (0 : ℝ) b, ∀ i j,
      g.inner (radialCurve (I := I) g p x t) (F i t) (F j t) =
        if i = j then (1 : ℝ) else 0)
    (hFdiff : ∀ i, ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x) (F i) t) t)
    (hJdiff : ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x)
          (radialJacobiField (I := I) g p x w) t) t)
    (hDJdiff : ∀ t ∈ Icc (0 : ℝ) b, DifferentiableAt ℝ
      (chartRepAt (I := I) (radialCurve (I := I) g p x)
        (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (radialJacobiField (I := I) g p x w) s) t) t)
    (hODE : ∀ t ∈ Ico (0 : ℝ) b,
      g.inner (radialCurve (I := I) g p x t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) s) t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) s) t)
      ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
        (radialJacobiField (I := I) g p x w t)
        (radialJacobiField (I := I) g p x w t))
    (hB :
      B ≤ Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) 0)) -
          gronwallBound 0 (max K 1)
            (K * (b * Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
              (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
                (radialJacobiField (I := I) g p x w) 0)
              (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
                (radialJacobiField (I := I) g p x w) 0)))) 1) :
    B ≤ Real.sqrt (g.inner (expMap (I := I) g p (show TangentSpace I p from x))
      (radialJacobiField (I := I) g p x w 1)
      (radialJacobiField (I := I) g p x w 1)) := by
  have hbounds := radialJacobi_one_bounds_at (I := I) g p x w hK hb h1b hγ hcard F
    hpar hON hFdiff hJdiff hDJdiff hODE
  have hlower :
      Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) 0)) -
          gronwallBound 0 (max K 1)
            (K * (b * Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
              (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
                (radialJacobiField (I := I) g p x w) 0)
              (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
                (radialJacobiField (I := I) g p x w) 0)))) 1 ≤
        Real.sqrt (g.inner (expMap (I := I) g p (show TangentSpace I p from x))
          (radialJacobiField (I := I) g p x w 1)
          (radialJacobiField (I := I) g p x w 1)) := by
    rw [← radialCurve_one (I := I) g p x]
    exact hbounds.2
  exact hB.trans hlower






omit [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem radialJacobi_one_ge
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E)
    {K b B : ℝ} (hK : 0 ≤ K) (hb : 0 ≤ b) (h1b : (1 : ℝ) ≤ b)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 (radialCurve (I := I) g p x))
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (hcard : ∀ t : ℝ,
      Fintype.card ι = Module.finrank ℝ (TangentSpace I (radialCurve (I := I) g p x t)))
    (F : ι → ∀ t : ℝ, TangentSpace I (radialCurve (I := I) g p x t))
    (hpar : ∀ i, ∀ t ∈ Icc (0 : ℝ) b,
      covDerivAlong (I := I) g (radialCurve (I := I) g p x) (F i) t = 0)
    (hON : ∀ t ∈ Icc (0 : ℝ) b, ∀ i j,
      g.inner (radialCurve (I := I) g p x t) (F i t) (F j t) =
        if i = j then (1 : ℝ) else 0)
    (hFdiff : ∀ i, ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x) (F i) t) t)
    (hJdiff : ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x)
          (radialJacobiField (I := I) g p x w) t) t)
    (hDJdiff : ∀ t ∈ Icc (0 : ℝ) b, DifferentiableAt ℝ
      (chartRepAt (I := I) (radialCurve (I := I) g p x)
        (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (radialJacobiField (I := I) g p x w) s) t) t)
    (hODE : ∀ t ∈ Ico (0 : ℝ) b,
      g.inner (radialCurve (I := I) g p x t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) s) t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) s) t)
      ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
        (radialJacobiField (I := I) g p x w t)
        (radialJacobiField (I := I) g p x w t))
    (hB :
      B ≤ Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) 0)) -
          gronwallBound 0 (max K 1)
            (K * (b * Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
              (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
                (radialJacobiField (I := I) g p x w) 0)
              (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
                (radialJacobiField (I := I) g p x w) 0)))) 1) :
    B ≤ Real.sqrt (g.inner (expMap (I := I) g p (show TangentSpace I p from x))
      (radialJacobiField (I := I) g p x w 1)
      (radialJacobiField (I := I) g p x w 1)) := by
  have hbounds := radialJacobi_one_bounds (I := I) g p x w hK hb h1b hγ hcard F
    hpar hON hFdiff hJdiff hDJdiff hODE
  have hlower :
      Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) 0)) -
          gronwallBound 0 (max K 1)
            (K * (b * Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
              (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
                (radialJacobiField (I := I) g p x w) 0)
              (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
                (radialJacobiField (I := I) g p x w) 0)))) 1 ≤
        Real.sqrt (g.inner (expMap (I := I) g p (show TangentSpace I p from x))
          (radialJacobiField (I := I) g p x w 1)
          (radialJacobiField (I := I) g p x w 1)) := by
    rw [← radialCurve_one (I := I) g p x]
    exact hbounds.2
  exact hB.trans hlower


omit [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem radialJacobi_sq_ge_at
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E)
    {K b B : ℝ} (hB_nonneg : 0 ≤ B)
    (hK : 0 ≤ K) (hb : 0 ≤ b) (h1b : (1 : ℝ) ≤ b)
    (hγ : ∀ t ∈ Icc (0 : ℝ) b,
      ContMDiffAt 𝓘(ℝ, ℝ) I 1 (radialCurve (I := I) g p x) t)
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (hcard : ∀ t : ℝ,
      Fintype.card ι = Module.finrank ℝ (TangentSpace I (radialCurve (I := I) g p x t)))
    (F : ι → ∀ t : ℝ, TangentSpace I (radialCurve (I := I) g p x t))
    (hpar : ∀ i, ∀ t ∈ Icc (0 : ℝ) b,
      covDerivAlong (I := I) g (radialCurve (I := I) g p x) (F i) t = 0)
    (hON : ∀ t ∈ Icc (0 : ℝ) b, ∀ i j,
      g.inner (radialCurve (I := I) g p x t) (F i t) (F j t) =
        if i = j then (1 : ℝ) else 0)
    (hFdiff : ∀ i, ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x) (F i) t) t)
    (hJdiff : ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x)
          (radialJacobiField (I := I) g p x w) t) t)
    (hDJdiff : ∀ t ∈ Icc (0 : ℝ) b, DifferentiableAt ℝ
      (chartRepAt (I := I) (radialCurve (I := I) g p x)
        (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (radialJacobiField (I := I) g p x w) s) t) t)
    (hODE : ∀ t ∈ Ico (0 : ℝ) b,
      g.inner (radialCurve (I := I) g p x t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) s) t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) s) t)
      ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
        (radialJacobiField (I := I) g p x w t)
        (radialJacobiField (I := I) g p x w t))
    (hB :
      B ≤ Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) 0)) -
          gronwallBound 0 (max K 1)
            (K * (b * Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
              (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
                (radialJacobiField (I := I) g p x w) 0)
              (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
                (radialJacobiField (I := I) g p x w) 0)))) 1) :
    B ^ 2 ≤ g.inner (expMap (I := I) g p (show TangentSpace I p from x))
      (radialJacobiField (I := I) g p x w 1)
      (radialJacobiField (I := I) g p x w 1) := by
  set q := radialCurve (I := I) g p x 1 with hq
  set J : TangentSpace I q := radialJacobiField (I := I) g p x w 1 with hJdef
  have hsqrt : B ≤ Real.sqrt (g.inner q J J) := by
    rw [hq, radialCurve_one]
    exact
      radialJacobi_one_ge_at (I := I) g p x w hK hb h1b hγ hcard F hpar hON
        hFdiff hJdiff hDJdiff hODE hB
  have hsq : B ^ 2 ≤ (Real.sqrt (g.inner q J J)) ^ 2 :=
    (sq_le_sq₀ hB_nonneg (Real.sqrt_nonneg _)).2 hsqrt
  have hJ_nonneg : 0 ≤ g.inner q J J := by
    rcases eq_or_ne J 0 with hJ | hJ
    · rw [hJ]
      have hzero :
          (g.inner q) (0 : TangentSpace I q) = (0 : TangentSpace I q →L[ℝ] ℝ) :=
        map_zero (g.inner q)
      rw [hzero]
      rfl
    · exact (g.pos q J hJ).le
  rw [← radialCurve_one (I := I) g p x]
  simpa [hq, hJdef] using hsq.trans_eq (Real.sq_sqrt hJ_nonneg)






omit [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem radialJacobi_sq_ge
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E)
    {K b B : ℝ} (hB_nonneg : 0 ≤ B)
    (hK : 0 ≤ K) (hb : 0 ≤ b) (h1b : (1 : ℝ) ≤ b)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 (radialCurve (I := I) g p x))
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (hcard : ∀ t : ℝ,
      Fintype.card ι = Module.finrank ℝ (TangentSpace I (radialCurve (I := I) g p x t)))
    (F : ι → ∀ t : ℝ, TangentSpace I (radialCurve (I := I) g p x t))
    (hpar : ∀ i, ∀ t ∈ Icc (0 : ℝ) b,
      covDerivAlong (I := I) g (radialCurve (I := I) g p x) (F i) t = 0)
    (hON : ∀ t ∈ Icc (0 : ℝ) b, ∀ i j,
      g.inner (radialCurve (I := I) g p x t) (F i t) (F j t) =
        if i = j then (1 : ℝ) else 0)
    (hFdiff : ∀ i, ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x) (F i) t) t)
    (hJdiff : ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x)
          (radialJacobiField (I := I) g p x w) t) t)
    (hDJdiff : ∀ t ∈ Icc (0 : ℝ) b, DifferentiableAt ℝ
      (chartRepAt (I := I) (radialCurve (I := I) g p x)
        (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (radialJacobiField (I := I) g p x w) s) t) t)
    (hODE : ∀ t ∈ Ico (0 : ℝ) b,
      g.inner (radialCurve (I := I) g p x t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) s) t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) s) t)
      ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
        (radialJacobiField (I := I) g p x w t)
        (radialJacobiField (I := I) g p x w t))
    (hB :
      B ≤ Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x w) 0)) -
          gronwallBound 0 (max K 1)
            (K * (b * Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
              (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
                (radialJacobiField (I := I) g p x w) 0)
              (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
                (radialJacobiField (I := I) g p x w) 0)))) 1) :
    B ^ 2 ≤ g.inner (expMap (I := I) g p (show TangentSpace I p from x))
      (radialJacobiField (I := I) g p x w 1)
      (radialJacobiField (I := I) g p x w 1) := by
  set q := radialCurve (I := I) g p x 1 with hq
  set J : TangentSpace I q := radialJacobiField (I := I) g p x w 1 with hJdef
  have hsqrt : B ≤ Real.sqrt (g.inner q J J) := by
    rw [hq, radialCurve_one]
    exact
      radialJacobi_one_ge (I := I) g p x w hK hb h1b hγ hcard F hpar hON
        hFdiff hJdiff hDJdiff hODE hB
  have hsq : B ^ 2 ≤ (Real.sqrt (g.inner q J J)) ^ 2 :=
    (sq_le_sq₀ hB_nonneg (Real.sqrt_nonneg _)).2 hsqrt
  have hJ_nonneg : 0 ≤ g.inner q J J := by
    rcases eq_or_ne J 0 with hJ | hJ
    · rw [hJ]
      have hzero :
          (g.inner q) (0 : TangentSpace I q) = (0 : TangentSpace I q →L[ℝ] ℝ) :=
        map_zero (g.inner q)
      rw [hzero]
      rfl
    · exact (g.pos q J hJ).le
  rw [← radialCurve_one (I := I) g p x]
  simpa [hq, hJdef] using hsq.trans_eq (Real.sq_sqrt hJ_nonneg)


omit [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem radialJacobi_dir_ge_at
    (g : SmoothRiemannianMetric I M) (p : M) (x : E)
    {K b B : ℝ} (hB_nonneg : 0 ≤ B)
    (hK : 0 ≤ K) (hb : 0 ≤ b) (h1b : (1 : ℝ) ≤ b)
    (hγ : ∀ t ∈ Icc (0 : ℝ) b,
      ContMDiffAt 𝓘(ℝ, ℝ) I 1 (radialCurve (I := I) g p x) t)
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (hcard : ∀ t : ℝ,
      Fintype.card ι = Module.finrank ℝ (TangentSpace I (radialCurve (I := I) g p x t)))
    (F : ι → ∀ t : ℝ, TangentSpace I (radialCurve (I := I) g p x t))
    (hpar : ∀ i, ∀ t ∈ Icc (0 : ℝ) b,
      covDerivAlong (I := I) g (radialCurve (I := I) g p x) (F i) t = 0)
    (hON : ∀ t ∈ Icc (0 : ℝ) b, ∀ i j,
      g.inner (radialCurve (I := I) g p x t) (F i t) (F j t) =
        if i = j then (1 : ℝ) else 0)
    (hFdiff : ∀ i, ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x) (F i) t) t)
    (hJdiff : ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
      ∀ t ∈ Icc (0 : ℝ) b,
        DifferentiableAt ℝ
          (chartRepAt (I := I) (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x
              (∑ i, v i • (chartModelBasis E) i)) t) t)
    (hDJdiff : ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
      ∀ t ∈ Icc (0 : ℝ) b, DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x
              (∑ i, v i • (chartModelBasis E) i)) s) t) t)
    (hODE : ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
      ∀ t ∈ Ico (0 : ℝ) b,
        g.inner (radialCurve (I := I) g p x t)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x
                (∑ i, v i • (chartModelBasis E) i)) s) t)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x
                (∑ i, v i • (chartModelBasis E) i)) s) t)
        ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
          (radialJacobiField (I := I) g p x
            (∑ i, v i • (chartModelBasis E) i) t)
          (radialJacobiField (I := I) g p x
            (∑ i, v i • (chartModelBasis E) i) t))
    (hB : ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
      B ≤ Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x
              (∑ i, v i • (chartModelBasis E) i)) 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x
              (∑ i, v i • (chartModelBasis E) i)) 0)) -
          gronwallBound 0 (max K 1)
            (K * (b * Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
              (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
                (radialJacobiField (I := I) g p x
                  (∑ i, v i • (chartModelBasis E) i)) 0)
              (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
                (radialJacobiField (I := I) g p x
                  (∑ i, v i • (chartModelBasis E) i)) 0)))) 1) :
    ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
      B ^ 2 ≤ g.inner (expMap (I := I) g p (show TangentSpace I p from x))
        (radialJacobiField (I := I) g p x
          (∑ i, v i • (chartModelBasis E) i) 1)
        (radialJacobiField (I := I) g p x
          (∑ i, v i • (chartModelBasis E) i) 1) := by
  intro v hv
  exact radialJacobi_sq_ge_at (I := I) g p x (∑ i, v i • (chartModelBasis E) i)
    hB_nonneg hK hb h1b hγ hcard F hpar hON hFdiff (hJdiff v hv)
    (hDJdiff v hv) (hODE v hv) (hB v hv)







omit [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem radialJacobi_dir_ge
    (g : SmoothRiemannianMetric I M) (p : M) (x : E)
    {K b B : ℝ} (hB_nonneg : 0 ≤ B)
    (hK : 0 ≤ K) (hb : 0 ≤ b) (h1b : (1 : ℝ) ≤ b)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 (radialCurve (I := I) g p x))
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (hcard : ∀ t : ℝ,
      Fintype.card ι = Module.finrank ℝ (TangentSpace I (radialCurve (I := I) g p x t)))
    (F : ι → ∀ t : ℝ, TangentSpace I (radialCurve (I := I) g p x t))
    (hpar : ∀ i, ∀ t ∈ Icc (0 : ℝ) b,
      covDerivAlong (I := I) g (radialCurve (I := I) g p x) (F i) t = 0)
    (hON : ∀ t ∈ Icc (0 : ℝ) b, ∀ i j,
      g.inner (radialCurve (I := I) g p x t) (F i t) (F j t) =
        if i = j then (1 : ℝ) else 0)
    (hFdiff : ∀ i, ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x) (F i) t) t)
    (hJdiff : ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
      ∀ t ∈ Icc (0 : ℝ) b,
        DifferentiableAt ℝ
          (chartRepAt (I := I) (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x
              (∑ i, v i • (chartModelBasis E) i)) t) t)
    (hDJdiff : ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
      ∀ t ∈ Icc (0 : ℝ) b, DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x
              (∑ i, v i • (chartModelBasis E) i)) s) t) t)
    (hODE : ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
      ∀ t ∈ Ico (0 : ℝ) b,
        g.inner (radialCurve (I := I) g p x t)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x
                (∑ i, v i • (chartModelBasis E) i)) s) t)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x
                (∑ i, v i • (chartModelBasis E) i)) s) t)
        ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
          (radialJacobiField (I := I) g p x
            (∑ i, v i • (chartModelBasis E) i) t)
          (radialJacobiField (I := I) g p x
            (∑ i, v i • (chartModelBasis E) i) t))
    (hB : ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
      B ≤ Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x
              (∑ i, v i • (chartModelBasis E) i)) 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x
              (∑ i, v i • (chartModelBasis E) i)) 0)) -
          gronwallBound 0 (max K 1)
            (K * (b * Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
              (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
                (radialJacobiField (I := I) g p x
                  (∑ i, v i • (chartModelBasis E) i)) 0)
              (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
                (radialJacobiField (I := I) g p x
                  (∑ i, v i • (chartModelBasis E) i)) 0)))) 1) :
    ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
      B ^ 2 ≤ g.inner (expMap (I := I) g p (show TangentSpace I p from x))
        (radialJacobiField (I := I) g p x
          (∑ i, v i • (chartModelBasis E) i) 1)
        (radialJacobiField (I := I) g p x
          (∑ i, v i • (chartModelBasis E) i) 1) := by
  intro v hv
  exact radialJacobi_sq_ge (I := I) g p x (∑ i, v i • (chartModelBasis E) i)
    hB_nonneg hK hb h1b hγ hcard F hpar hON hFdiff (hJdiff v hv)
    (hDJdiff v hv) (hODE v hv) (hB v hv)


omit [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem radialJacobi_fin_le_at
    (g : SmoothRiemannianMetric I M) (p : M) (x : E)
    {K b B : ℝ} (hK : 0 ≤ K) (hb : 0 ≤ b) (h1b : (1 : ℝ) ≤ b)
    (hγ : ∀ t ∈ Icc (0 : ℝ) b,
      ContMDiffAt 𝓘(ℝ, ℝ) I 1 (radialCurve (I := I) g p x) t)
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (hcard : ∀ t : ℝ,
      Fintype.card ι = Module.finrank ℝ (TangentSpace I (radialCurve (I := I) g p x t)))
    (F : ι → ∀ t : ℝ, TangentSpace I (radialCurve (I := I) g p x t))
    (hpar : ∀ i, ∀ t ∈ Icc (0 : ℝ) b,
      covDerivAlong (I := I) g (radialCurve (I := I) g p x) (F i) t = 0)
    (hON : ∀ t ∈ Icc (0 : ℝ) b, ∀ i j,
      g.inner (radialCurve (I := I) g p x t) (F i t) (F j t) =
        if i = j then (1 : ℝ) else 0)
    (hFdiff : ∀ i, ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x) (F i) t) t)
    (hJdiff : ∀ k : Fin (Module.finrank ℝ E), ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x)
          (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) t) t)
    (hDJdiff : ∀ k : Fin (Module.finrank ℝ E), ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) s) t) t)
    (hODE : ∀ k : Fin (Module.finrank ℝ E), ∀ t ∈ Ico (0 : ℝ) b,
      g.inner (radialCurve (I := I) g p x t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) s) t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) s) t)
      ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
        (radialJacobiField (I := I) g p x ((chartModelBasis E) k) t)
        (radialJacobiField (I := I) g p x ((chartModelBasis E) k) t))
    (hB : ∀ k : Fin (Module.finrank ℝ E),
      Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) 0)) +
          gronwallBound 0 (max K 1)
            (K * (b * Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
              (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
                (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) 0)
              (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
                (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) 0)))) 1 ≤ B) :
    ∀ k : Fin (Module.finrank ℝ E),
      Real.sqrt (g.inner (expMap (I := I) g p (show TangentSpace I p from x))
        (radialJacobiField (I := I) g p x ((chartModelBasis E) k) 1)
        (radialJacobiField (I := I) g p x ((chartModelBasis E) k) 1)) ≤ B := by
  intro k
  exact radialJacobi_one_le_at (I := I) g p x ((chartModelBasis E) k) hK hb h1b hγ
    hcard F hpar hON hFdiff (hJdiff k) (hDJdiff k) (hODE k) (hB k)





omit [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem radialJacobi_fin_le
    (g : SmoothRiemannianMetric I M) (p : M) (x : E)
    {K b B : ℝ} (hK : 0 ≤ K) (hb : 0 ≤ b) (h1b : (1 : ℝ) ≤ b)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 (radialCurve (I := I) g p x))
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (hcard : ∀ t : ℝ,
      Fintype.card ι = Module.finrank ℝ (TangentSpace I (radialCurve (I := I) g p x t)))
    (F : ι → ∀ t : ℝ, TangentSpace I (radialCurve (I := I) g p x t))
    (hpar : ∀ i, ∀ t ∈ Icc (0 : ℝ) b,
      covDerivAlong (I := I) g (radialCurve (I := I) g p x) (F i) t = 0)
    (hON : ∀ t ∈ Icc (0 : ℝ) b, ∀ i j,
      g.inner (radialCurve (I := I) g p x t) (F i t) (F j t) =
        if i = j then (1 : ℝ) else 0)
    (hFdiff : ∀ i, ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x) (F i) t) t)
    (hJdiff : ∀ k : Fin (Module.finrank ℝ E), ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x)
          (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) t) t)
    (hDJdiff : ∀ k : Fin (Module.finrank ℝ E), ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) s) t) t)
    (hODE : ∀ k : Fin (Module.finrank ℝ E), ∀ t ∈ Ico (0 : ℝ) b,
      g.inner (radialCurve (I := I) g p x t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) s) t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) s) t)
      ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
        (radialJacobiField (I := I) g p x ((chartModelBasis E) k) t)
        (radialJacobiField (I := I) g p x ((chartModelBasis E) k) t))
    (hB : ∀ k : Fin (Module.finrank ℝ E),
      Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) 0)) +
          gronwallBound 0 (max K 1)
            (K * (b * Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
              (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
                (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) 0)
              (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
                (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) 0)))) 1 ≤ B) :
    ∀ k : Fin (Module.finrank ℝ E),
      Real.sqrt (g.inner (expMap (I := I) g p (show TangentSpace I p from x))
        (radialJacobiField (I := I) g p x ((chartModelBasis E) k) 1)
        (radialJacobiField (I := I) g p x ((chartModelBasis E) k) 1)) ≤ B := by
  intro k
  exact radialJacobi_one_le (I := I) g p x ((chartModelBasis E) k) hK hb h1b hγ
    hcard F hpar hON hFdiff (hJdiff k) (hDJdiff k) (hODE k) (hB k)


omit [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem radialJacobi_fin_le_of_init_bound_at
    (g : SmoothRiemannianMetric I M) (p : M) (x : E)
    {K b A B : ℝ} (hK : 0 ≤ K) (hb : 0 ≤ b) (h1b : (1 : ℝ) ≤ b)
    (hγ : ∀ t ∈ Icc (0 : ℝ) b,
      ContMDiffAt 𝓘(ℝ, ℝ) I 1 (radialCurve (I := I) g p x) t)
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (hcard : ∀ t : ℝ,
      Fintype.card ι = Module.finrank ℝ (TangentSpace I (radialCurve (I := I) g p x t)))
    (F : ι → ∀ t : ℝ, TangentSpace I (radialCurve (I := I) g p x t))
    (hpar : ∀ i, ∀ t ∈ Icc (0 : ℝ) b,
      covDerivAlong (I := I) g (radialCurve (I := I) g p x) (F i) t = 0)
    (hON : ∀ t ∈ Icc (0 : ℝ) b, ∀ i j,
      g.inner (radialCurve (I := I) g p x t) (F i t) (F j t) =
        if i = j then (1 : ℝ) else 0)
    (hFdiff : ∀ i, ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x) (F i) t) t)
    (hJdiff : ∀ k : Fin (Module.finrank ℝ E), ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x)
          (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) t) t)
    (hDJdiff : ∀ k : Fin (Module.finrank ℝ E), ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) s) t) t)
    (hODE : ∀ k : Fin (Module.finrank ℝ E), ∀ t ∈ Ico (0 : ℝ) b,
      g.inner (radialCurve (I := I) g p x t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) s) t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) s) t)
      ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
        (radialJacobiField (I := I) g p x ((chartModelBasis E) k) t)
        (radialJacobiField (I := I) g p x ((chartModelBasis E) k) t))
    (hinit : ∀ k : Fin (Module.finrank ℝ E),
      Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) 0)) ≤ A)
    (hmodel :
      A + gronwallBound 0 (max K 1) (K * (b * A)) 1 ≤ B) :
    ∀ k : Fin (Module.finrank ℝ E),
      Real.sqrt (g.inner (expMap (I := I) g p (show TangentSpace I p from x))
        (radialJacobiField (I := I) g p x ((chartModelBasis E) k) 1)
        (radialJacobiField (I := I) g p x ((chartModelBasis E) k) 1)) ≤ B := by
  refine radialJacobi_fin_le_at (I := I) g p x hK hb h1b hγ hcard F hpar hON
    hFdiff hJdiff hDJdiff hODE ?_
  intro k
  set vnorm : ℝ :=
    Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
      (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
        (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) 0)
      (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
        (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) 0))
  have hvA : vnorm ≤ A := by
    simpa [vnorm] using hinit k
  have heps :
      K * (b * vnorm) ≤ K * (b * A) := by
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hvA hb) hK
  have hmax : 0 ≤ max K 1 := le_max_of_le_right (by norm_num : (0 : ℝ) ≤ 1)
  have hgb :
      gronwallBound 0 (max K 1) (K * (b * vnorm)) 1 ≤
        gronwallBound 0 (max K 1) (K * (b * A)) 1 :=
    gronwallBound_zero_mono_eps hmax (by norm_num) heps
  calc
    vnorm + gronwallBound 0 (max K 1) (K * (b * vnorm)) 1
        ≤ A + gronwallBound 0 (max K 1) (K * (b * A)) 1 :=
          add_le_add hvA hgb
    _ ≤ B := hmodel







omit [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem radialJacobi_fin_le_of_init_bound
    (g : SmoothRiemannianMetric I M) (p : M) (x : E)
    {K b A B : ℝ} (hK : 0 ≤ K) (hb : 0 ≤ b) (h1b : (1 : ℝ) ≤ b)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 (radialCurve (I := I) g p x))
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (hcard : ∀ t : ℝ,
      Fintype.card ι = Module.finrank ℝ (TangentSpace I (radialCurve (I := I) g p x t)))
    (F : ι → ∀ t : ℝ, TangentSpace I (radialCurve (I := I) g p x t))
    (hpar : ∀ i, ∀ t ∈ Icc (0 : ℝ) b,
      covDerivAlong (I := I) g (radialCurve (I := I) g p x) (F i) t = 0)
    (hON : ∀ t ∈ Icc (0 : ℝ) b, ∀ i j,
      g.inner (radialCurve (I := I) g p x t) (F i t) (F j t) =
        if i = j then (1 : ℝ) else 0)
    (hFdiff : ∀ i, ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x) (F i) t) t)
    (hJdiff : ∀ k : Fin (Module.finrank ℝ E), ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x)
          (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) t) t)
    (hDJdiff : ∀ k : Fin (Module.finrank ℝ E), ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) s) t) t)
    (hODE : ∀ k : Fin (Module.finrank ℝ E), ∀ t ∈ Ico (0 : ℝ) b,
      g.inner (radialCurve (I := I) g p x t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) s) t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) s) t)
      ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
        (radialJacobiField (I := I) g p x ((chartModelBasis E) k) t)
        (radialJacobiField (I := I) g p x ((chartModelBasis E) k) t))
    (hinit : ∀ k : Fin (Module.finrank ℝ E),
      Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) 0)) ≤ A)
    (hmodel :
      A + gronwallBound 0 (max K 1) (K * (b * A)) 1 ≤ B) :
    ∀ k : Fin (Module.finrank ℝ E),
      Real.sqrt (g.inner (expMap (I := I) g p (show TangentSpace I p from x))
        (radialJacobiField (I := I) g p x ((chartModelBasis E) k) 1)
        (radialJacobiField (I := I) g p x ((chartModelBasis E) k) 1)) ≤ B := by
  refine radialJacobi_fin_le (I := I) g p x hK hb h1b hγ hcard F hpar hON
    hFdiff hJdiff hDJdiff hODE ?_
  intro k
  set vnorm : ℝ :=
    Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
      (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
        (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) 0)
      (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
        (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) 0))
  have hvA : vnorm ≤ A := by
    simpa [vnorm] using hinit k
  have heps :
      K * (b * vnorm) ≤ K * (b * A) := by
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hvA hb) hK
  have hmax : 0 ≤ max K 1 := le_max_of_le_right (by norm_num : (0 : ℝ) ≤ 1)
  have hgb :
      gronwallBound 0 (max K 1) (K * (b * vnorm)) 1 ≤
        gronwallBound 0 (max K 1) (K * (b * A)) 1 :=
    gronwallBound_zero_mono_eps hmax (by norm_num) heps
  calc
    vnorm + gronwallBound 0 (max K 1) (K * (b * vnorm)) 1
        ≤ A + gronwallBound 0 (max K 1) (K * (b * A)) 1 :=
          add_le_add hvA hgb
    _ ≤ B := hmodel








omit [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma radialJacobi_init_le_of_deriv_eq
    (g : SmoothRiemannianMetric I M) (p : M) (x : E) {A : ℝ}
    (hderiv : ∀ k : Fin (Module.finrank ℝ E),
      (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
        (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) 0 : E) =
        (chartModelBasis E) k)
    (hbasis : ∀ k : Fin (Module.finrank ℝ E),
      Real.sqrt (g.inner p ((chartModelBasis E) k) ((chartModelBasis E) k)) ≤ A) :
    ∀ k : Fin (Module.finrank ℝ E),
      Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) 0)) ≤ A := by
  intro k
  rw [radialCurve_zero (I := I) g p x]
  rw [hderiv k]
  exact hbasis k







omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
lemma fin_deriv_radius
    (g : SmoothRiemannianMetric I M) (p : M) {r : ℝ} (x : E)
    (hderivRadius : ∀ x w : E, ‖x‖ < r → ‖w‖ < r →
      (covDerivAlong (I := I) g
        (fun v : ℝ => (expMap (I := I) g p (show TangentSpace I p from (v • x)) : M))
        (radialJacobiField (I := I) g p x w) 0 : E) = w)
    (hx : ‖x‖ < r)
    (hbasisSmall : ∀ k : Fin (Module.finrank ℝ E), ‖(chartModelBasis E) k‖ < r) :
    ∀ k : Fin (Module.finrank ℝ E),
      (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
        (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) 0 : E) =
        (chartModelBasis E) k := by
  intro k
  simpa [radialCurve] using hderivRadius x ((chartModelBasis E) k) hx (hbasisSmall k)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
private lemma sqrt_inner_le_of_smul_le
    (g : SmoothRiemannianMetric I M) (q : M) (v : TangentSpace I q)
    {a B : ℝ} (ha : 0 < a)
    (h : Real.sqrt (g.inner q (a • v) (a • v)) ≤ a * B) :
    Real.sqrt (g.inner q v v) ≤ B := by
  have hscale :
      g.inner q (a • v) (a • v) = a ^ 2 * g.inner q v v := by
    rw [map_smul (g.inner q), ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.map_smul, smul_eq_mul, smul_eq_mul]
    ring
  have hsqrt :
      Real.sqrt (a ^ 2 * g.inner q v v) =
        a * Real.sqrt (g.inner q v v) := by
    rw [Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq_eq_abs, abs_of_pos ha]
  rw [hscale, hsqrt] at h
  exact (le_of_mul_le_mul_left h ha)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
private lemma le_sqrt_inner_of_smul_ge
    (g : SmoothRiemannianMetric I M) (q : M) (v : TangentSpace I q)
    {a B : ℝ} (ha : 0 < a)
    (h : a * B ≤ Real.sqrt (g.inner q (a • v) (a • v))) :
    B ≤ Real.sqrt (g.inner q v v) := by
  have hscale :
      g.inner q (a • v) (a • v) = a ^ 2 * g.inner q v v := by
    rw [map_smul (g.inner q), ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.map_smul, smul_eq_mul, smul_eq_mul]
    ring
  have hsqrt :
      Real.sqrt (a ^ 2 * g.inner q v v) =
        a * Real.sqrt (g.inner q v v) := by
    rw [Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq_eq_abs, abs_of_pos ha]
  rw [hscale, hsqrt] at h
  exact le_of_mul_le_mul_left h ha








omit [T2Space M] [SigmaCompactSpace M] in
lemma radialJacobi_one_le_of_smul
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E)
    {a B : ℝ} (ha : 0 < a)
    (hxrad : ‖x‖ < expMapC2Radius (I := I) g p)
    (hscaled :
      Real.sqrt (g.inner (expMap (I := I) g p (show TangentSpace I p from x))
        (radialJacobiField (I := I) g p x (a • w) 1)
        (radialJacobiField (I := I) g p x (a • w) 1)) ≤ a * B) :
    Real.sqrt (g.inner (expMap (I := I) g p (show TangentSpace I p from x))
      (radialJacobiField (I := I) g p x w 1)
      (radialJacobiField (I := I) g p x w 1)) ≤ B := by
  have hsmul := radialJacobi_one_smul (I := I) g p x w a hxrad
  rw [hsmul] at hscaled
  exact sqrt_inner_le_of_smul_le (I := I) g
    (expMap (I := I) g p (show TangentSpace I p from x))
    (radialJacobiField (I := I) g p x w 1) ha hscaled




omit [T2Space M] [SigmaCompactSpace M] in
lemma radialJacobi_one_ge_of_smul
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E)
    {a B : ℝ} (ha : 0 < a)
    (hxrad : ‖x‖ < expMapC2Radius (I := I) g p)
    (hscaled :
      a * B ≤ Real.sqrt (g.inner (expMap (I := I) g p (show TangentSpace I p from x))
        (radialJacobiField (I := I) g p x (a • w) 1)
        (radialJacobiField (I := I) g p x (a • w) 1))) :
    B ≤ Real.sqrt (g.inner (expMap (I := I) g p (show TangentSpace I p from x))
      (radialJacobiField (I := I) g p x w 1)
      (radialJacobiField (I := I) g p x w 1)) := by
  have hsmul := radialJacobi_one_smul (I := I) g p x w a hxrad
  rw [hsmul] at hscaled
  exact le_sqrt_inner_of_smul_ge (I := I) g
    (expMap (I := I) g p (show TangentSpace I p from x))
    (radialJacobiField (I := I) g p x w 1) ha hscaled

private noncomputable def basisNormSup : ℝ :=
  (Finset.univ : Finset (Fin (Module.finrank ℝ E))).sup'
    (by
      refine Finset.univ_nonempty_iff.mpr ?_
      exact ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne _)⟩⟩)
    (fun k => ‖(chartModelBasis E) k‖)

private lemma basisNormSup_nonneg : 0 ≤ basisNormSup (E := E) := by
  classical
  unfold basisNormSup
  have hne : (Finset.univ : Finset (Fin (Module.finrank ℝ E))).Nonempty := by
    refine Finset.univ_nonempty_iff.mpr ?_
    exact ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne _)⟩⟩
  obtain ⟨k₀, hk₀⟩ := hne
  have hnn : (0 : ℝ) ≤ ‖(chartModelBasis E) k₀‖ := norm_nonneg _
  exact hnn.trans (Finset.le_sup'
    (f := fun k => ‖(chartModelBasis E) k‖) hk₀)

private lemma norm_basis_le_sup
    (k : Fin (Module.finrank ℝ E)) :
    ‖(chartModelBasis E) k‖ ≤ basisNormSup (E := E) := by
  classical
  unfold basisNormSup
  exact Finset.le_sup'
    (f := fun k => ‖(chartModelBasis E) k‖)
    (Finset.mem_univ _)



lemma basisScaleSmall {r : ℝ} (hr : 0 < r) :
    ∃ a : ℝ, 0 < a ∧
      ∀ k : Fin (Module.finrank ℝ E), ‖a • (chartModelBasis E) k‖ < r := by
  classical
  set C : ℝ := basisNormSup (E := E) with hC
  have hC_nonneg : 0 ≤ C := by
    simpa [hC] using basisNormSup_nonneg (E := E)
  have hden_pos : 0 < C + 1 := by linarith
  refine ⟨r / (C + 1), div_pos hr hden_pos, ?_⟩
  intro k
  have hscale_pos : 0 < r / (C + 1) := div_pos hr hden_pos
  have hk_le : ‖(chartModelBasis E) k‖ ≤ C := by
    simpa [hC] using norm_basis_le_sup (E := E) k
  have hk_lt : ‖(chartModelBasis E) k‖ < C + 1 := lt_of_le_of_lt hk_le (by linarith)
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hscale_pos]
  calc
    r / (C + 1) * ‖(chartModelBasis E) k‖
        < r / (C + 1) * (C + 1) :=
          mul_lt_mul_of_pos_left hk_lt hscale_pos
    _ = r := by field_simp [ne_of_gt hden_pos]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma scaleSmall_of_le {a b r : ℝ} {v : E}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a ≤ b) (hsmall : ‖b • v‖ < r) :
    ‖a • v‖ < r := by
  rw [norm_smul] at hsmall
  rw [norm_smul]
  have habs : ‖a‖ ≤ ‖b‖ := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb]
    exact hab
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right habs (norm_nonneg v)) hsmall



lemma basisUnitScaleSmall {r : ℝ} (hr : 0 < r) :
    ∃ a : ℝ, 0 < a ∧
      (∀ k : Fin (Module.finrank ℝ E), ‖a • (chartModelBasis E) k‖ < r) ∧
      (∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
        ‖a • (∑ i, v i • (chartModelBasis E) i)‖ < r) := by
  obtain ⟨ab, hab_pos, hbasis⟩ := basisScaleSmall (E := E) hr
  obtain ⟨ad, had_pos, hdir⟩ := unitDirScaleSmall (E := E) hr
  refine ⟨min ab ad, lt_min hab_pos had_pos, ?_, ?_⟩
  · intro k
    exact scaleSmall_of_le
      (v := (chartModelBasis E) k)
      (le_of_lt (lt_min hab_pos had_pos))
      (le_of_lt hab_pos)
      (min_le_left ab ad)
      (hbasis k)
  · intro v hv
    exact scaleSmall_of_le
      (v := ∑ i, v i • (chartModelBasis E) i)
      (le_of_lt (lt_min hab_pos had_pos))
      (le_of_lt had_pos)
      (min_le_right ab ad)
      (hdir v hv)



omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
lemma basisInit_smul_le
    (g : SmoothRiemannianMetric I M) (p : M) {a A : ℝ} (ha : 0 < a)
    (hbasis : ∀ k : Fin (Module.finrank ℝ E),
      Real.sqrt (g.inner p ((chartModelBasis E) k) ((chartModelBasis E) k)) ≤ A) :
    ∀ k : Fin (Module.finrank ℝ E),
      Real.sqrt (g.inner p (a • (chartModelBasis E) k) (a • (chartModelBasis E) k)) ≤
        a * A := by
  intro k
  let v : TangentSpace I p := (chartModelBasis E) k
  have hscale :
      g.inner p (a • (chartModelBasis E) k) (a • (chartModelBasis E) k) =
        a ^ 2 * g.inner p ((chartModelBasis E) k) ((chartModelBasis E) k) := by
    have hscale_v : g.inner p (a • v) (a • v) = a ^ 2 * g.inner p v v := by
      rw [map_smul (g.inner p), ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.map_smul, smul_eq_mul, smul_eq_mul]
      ring
    change g.inner p (a • v) (a • v) = a ^ 2 * g.inner p v v
    exact hscale_v
  have hsqrt :
      Real.sqrt (a ^ 2 * g.inner p ((chartModelBasis E) k) ((chartModelBasis E) k)) =
        a * Real.sqrt (g.inner p ((chartModelBasis E) k) ((chartModelBasis E) k)) := by
    rw [Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq_eq_abs, abs_of_pos ha]
  rw [hscale, hsqrt]
  exact mul_le_mul_of_nonneg_left (hbasis k) ha.le



lemma model_le_smul {a K b A B : ℝ} (ha : 0 < a)
    (hmodel : A + gronwallBound 0 (max K 1) (K * (b * A)) 1 ≤ B) :
    a * A + gronwallBound 0 (max K 1) (K * (b * (a * A))) 1 ≤ a * B := by
  have herr :
      gronwallBound 0 (max K 1) (K * (b * (a * A))) 1 =
        a * gronwallBound 0 (max K 1) (K * (b * A)) 1 := by
    have heps : K * (b * (a * A)) = a * (K * (b * A)) := by ring
    rw [heps, gronwallBound_zero_mul_eps]
  rw [herr]
  have hmul := mul_le_mul_of_nonneg_left hmodel ha.le
  nlinarith


omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
lemma basisModel_le_smul
    (g : SmoothRiemannianMetric I M) (p : M) {a K b A B : ℝ} (ha : 0 < a)
    (hbasis : ∀ k : Fin (Module.finrank ℝ E),
      Real.sqrt (g.inner p ((chartModelBasis E) k) ((chartModelBasis E) k)) ≤ A)
    (hmodel : A + gronwallBound 0 (max K 1) (K * (b * A)) 1 ≤ B) :
    (∀ k : Fin (Module.finrank ℝ E),
      Real.sqrt (g.inner p (a • (chartModelBasis E) k) (a • (chartModelBasis E) k)) ≤
        a * A) ∧
    a * A + gronwallBound 0 (max K 1) (K * (b * (a * A))) 1 ≤ a * B := by
  exact ⟨basisInit_smul_le (I := I) g p ha hbasis, model_le_smul ha hmodel⟩


omit [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem radialJacobi_fin_le_of_deriv_eq_at
    (g : SmoothRiemannianMetric I M) (p : M) (x : E)
    {K b A B : ℝ} (hK : 0 ≤ K) (hb : 0 ≤ b) (h1b : (1 : ℝ) ≤ b)
    (hγ : ∀ t ∈ Icc (0 : ℝ) b,
      ContMDiffAt 𝓘(ℝ, ℝ) I 1 (radialCurve (I := I) g p x) t)
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (hcard : ∀ t : ℝ,
      Fintype.card ι = Module.finrank ℝ (TangentSpace I (radialCurve (I := I) g p x t)))
    (F : ι → ∀ t : ℝ, TangentSpace I (radialCurve (I := I) g p x t))
    (hpar : ∀ i, ∀ t ∈ Icc (0 : ℝ) b,
      covDerivAlong (I := I) g (radialCurve (I := I) g p x) (F i) t = 0)
    (hON : ∀ t ∈ Icc (0 : ℝ) b, ∀ i j,
      g.inner (radialCurve (I := I) g p x t) (F i t) (F j t) =
        if i = j then (1 : ℝ) else 0)
    (hFdiff : ∀ i, ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x) (F i) t) t)
    (hJdiff : ∀ k : Fin (Module.finrank ℝ E), ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x)
          (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) t) t)
    (hDJdiff : ∀ k : Fin (Module.finrank ℝ E), ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) s) t) t)
    (hODE : ∀ k : Fin (Module.finrank ℝ E), ∀ t ∈ Ico (0 : ℝ) b,
      g.inner (radialCurve (I := I) g p x t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) s) t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) s) t)
      ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
        (radialJacobiField (I := I) g p x ((chartModelBasis E) k) t)
        (radialJacobiField (I := I) g p x ((chartModelBasis E) k) t))
    (hderiv : ∀ k : Fin (Module.finrank ℝ E),
      (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
        (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) 0 : E) =
        (chartModelBasis E) k)
    (hbasis : ∀ k : Fin (Module.finrank ℝ E),
      Real.sqrt (g.inner p ((chartModelBasis E) k) ((chartModelBasis E) k)) ≤ A)
    (hmodel :
      A + gronwallBound 0 (max K 1) (K * (b * A)) 1 ≤ B) :
    ∀ k : Fin (Module.finrank ℝ E),
      Real.sqrt (g.inner (expMap (I := I) g p (show TangentSpace I p from x))
        (radialJacobiField (I := I) g p x ((chartModelBasis E) k) 1)
        (radialJacobiField (I := I) g p x ((chartModelBasis E) k) 1)) ≤ B :=
  radialJacobi_fin_le_of_init_bound_at (I := I) g p x hK hb h1b hγ hcard F hpar hON
    hFdiff hJdiff hDJdiff hODE
    (radialJacobi_init_le_of_deriv_eq (I := I) g p x hderiv hbasis) hmodel








omit [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem radialJacobi_fin_le_of_deriv_eq
    (g : SmoothRiemannianMetric I M) (p : M) (x : E)
    {K b A B : ℝ} (hK : 0 ≤ K) (hb : 0 ≤ b) (h1b : (1 : ℝ) ≤ b)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 (radialCurve (I := I) g p x))
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (hcard : ∀ t : ℝ,
      Fintype.card ι = Module.finrank ℝ (TangentSpace I (radialCurve (I := I) g p x t)))
    (F : ι → ∀ t : ℝ, TangentSpace I (radialCurve (I := I) g p x t))
    (hpar : ∀ i, ∀ t ∈ Icc (0 : ℝ) b,
      covDerivAlong (I := I) g (radialCurve (I := I) g p x) (F i) t = 0)
    (hON : ∀ t ∈ Icc (0 : ℝ) b, ∀ i j,
      g.inner (radialCurve (I := I) g p x t) (F i t) (F j t) =
        if i = j then (1 : ℝ) else 0)
    (hFdiff : ∀ i, ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x) (F i) t) t)
    (hJdiff : ∀ k : Fin (Module.finrank ℝ E), ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x)
          (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) t) t)
    (hDJdiff : ∀ k : Fin (Module.finrank ℝ E), ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) s) t) t)
    (hODE : ∀ k : Fin (Module.finrank ℝ E), ∀ t ∈ Ico (0 : ℝ) b,
      g.inner (radialCurve (I := I) g p x t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) s) t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) s) t)
      ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
        (radialJacobiField (I := I) g p x ((chartModelBasis E) k) t)
        (radialJacobiField (I := I) g p x ((chartModelBasis E) k) t))
    (hderiv : ∀ k : Fin (Module.finrank ℝ E),
      (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
        (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) 0 : E) =
        (chartModelBasis E) k)
    (hbasis : ∀ k : Fin (Module.finrank ℝ E),
      Real.sqrt (g.inner p ((chartModelBasis E) k) ((chartModelBasis E) k)) ≤ A)
    (hmodel :
      A + gronwallBound 0 (max K 1) (K * (b * A)) 1 ≤ B) :
    ∀ k : Fin (Module.finrank ℝ E),
      Real.sqrt (g.inner (expMap (I := I) g p (show TangentSpace I p from x))
        (radialJacobiField (I := I) g p x ((chartModelBasis E) k) 1)
        (radialJacobiField (I := I) g p x ((chartModelBasis E) k) 1)) ≤ B :=
  radialJacobi_fin_le_of_deriv_eq_at (I := I) g p x hK hb h1b
    (fun _ _ => hγ.contMDiffAt) hcard F hpar hON
    hFdiff hJdiff hDJdiff hODE
    hderiv hbasis hmodel


omit [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem radialJacobi_fin_le_of_radius_deriv_at
    (g : SmoothRiemannianMetric I M) (p : M) (x : E)
    {r K b A B : ℝ} (hK : 0 ≤ K) (hb : 0 ≤ b) (h1b : (1 : ℝ) ≤ b)
    (hγ : ∀ t ∈ Icc (0 : ℝ) b,
      ContMDiffAt 𝓘(ℝ, ℝ) I 1 (radialCurve (I := I) g p x) t)
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (hcard : ∀ t : ℝ,
      Fintype.card ι = Module.finrank ℝ (TangentSpace I (radialCurve (I := I) g p x t)))
    (F : ι → ∀ t : ℝ, TangentSpace I (radialCurve (I := I) g p x t))
    (hpar : ∀ i, ∀ t ∈ Icc (0 : ℝ) b,
      covDerivAlong (I := I) g (radialCurve (I := I) g p x) (F i) t = 0)
    (hON : ∀ t ∈ Icc (0 : ℝ) b, ∀ i j,
      g.inner (radialCurve (I := I) g p x t) (F i t) (F j t) =
        if i = j then (1 : ℝ) else 0)
    (hFdiff : ∀ i, ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x) (F i) t) t)
    (hJdiff : ∀ k : Fin (Module.finrank ℝ E), ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x)
          (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) t) t)
    (hDJdiff : ∀ k : Fin (Module.finrank ℝ E), ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) s) t) t)
    (hODE : ∀ k : Fin (Module.finrank ℝ E), ∀ t ∈ Ico (0 : ℝ) b,
      g.inner (radialCurve (I := I) g p x t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) s) t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) s) t)
      ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
        (radialJacobiField (I := I) g p x ((chartModelBasis E) k) t)
        (radialJacobiField (I := I) g p x ((chartModelBasis E) k) t))
    (hderivRadius : ∀ x w : E, ‖x‖ < r → ‖w‖ < r →
      (covDerivAlong (I := I) g
        (fun v : ℝ => (expMap (I := I) g p (show TangentSpace I p from (v • x)) : M))
        (radialJacobiField (I := I) g p x w) 0 : E) = w)
    (hx : ‖x‖ < r)
    (hbasisSmall : ∀ k : Fin (Module.finrank ℝ E), ‖(chartModelBasis E) k‖ < r)
    (hbasis : ∀ k : Fin (Module.finrank ℝ E),
      Real.sqrt (g.inner p ((chartModelBasis E) k) ((chartModelBasis E) k)) ≤ A)
    (hmodel :
      A + gronwallBound 0 (max K 1) (K * (b * A)) 1 ≤ B) :
    ∀ k : Fin (Module.finrank ℝ E),
      Real.sqrt (g.inner (expMap (I := I) g p (show TangentSpace I p from x))
        (radialJacobiField (I := I) g p x ((chartModelBasis E) k) 1)
        (radialJacobiField (I := I) g p x ((chartModelBasis E) k) 1)) ≤ B :=
  radialJacobi_fin_le_of_deriv_eq_at (I := I) g p x hK hb h1b hγ hcard F hpar hON
    hFdiff hJdiff hDJdiff hODE
    (fin_deriv_radius (I := I) g p x hderivRadius hx hbasisSmall)
    hbasis hmodel






omit [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem radialJacobi_fin_le_of_radius_deriv
    (g : SmoothRiemannianMetric I M) (p : M) (x : E)
    {r K b A B : ℝ} (hK : 0 ≤ K) (hb : 0 ≤ b) (h1b : (1 : ℝ) ≤ b)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 (radialCurve (I := I) g p x))
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (hcard : ∀ t : ℝ,
      Fintype.card ι = Module.finrank ℝ (TangentSpace I (radialCurve (I := I) g p x t)))
    (F : ι → ∀ t : ℝ, TangentSpace I (radialCurve (I := I) g p x t))
    (hpar : ∀ i, ∀ t ∈ Icc (0 : ℝ) b,
      covDerivAlong (I := I) g (radialCurve (I := I) g p x) (F i) t = 0)
    (hON : ∀ t ∈ Icc (0 : ℝ) b, ∀ i j,
      g.inner (radialCurve (I := I) g p x t) (F i t) (F j t) =
        if i = j then (1 : ℝ) else 0)
    (hFdiff : ∀ i, ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x) (F i) t) t)
    (hJdiff : ∀ k : Fin (Module.finrank ℝ E), ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x)
          (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) t) t)
    (hDJdiff : ∀ k : Fin (Module.finrank ℝ E), ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) s) t) t)
    (hODE : ∀ k : Fin (Module.finrank ℝ E), ∀ t ∈ Ico (0 : ℝ) b,
      g.inner (radialCurve (I := I) g p x t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) s) t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x ((chartModelBasis E) k)) s) t)
      ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
        (radialJacobiField (I := I) g p x ((chartModelBasis E) k) t)
        (radialJacobiField (I := I) g p x ((chartModelBasis E) k) t))
    (hderivRadius : ∀ x w : E, ‖x‖ < r → ‖w‖ < r →
      (covDerivAlong (I := I) g
        (fun v : ℝ => (expMap (I := I) g p (show TangentSpace I p from (v • x)) : M))
        (radialJacobiField (I := I) g p x w) 0 : E) = w)
    (hx : ‖x‖ < r)
    (hbasisSmall : ∀ k : Fin (Module.finrank ℝ E), ‖(chartModelBasis E) k‖ < r)
    (hbasis : ∀ k : Fin (Module.finrank ℝ E),
      Real.sqrt (g.inner p ((chartModelBasis E) k) ((chartModelBasis E) k)) ≤ A)
    (hmodel :
      A + gronwallBound 0 (max K 1) (K * (b * A)) 1 ≤ B) :
    ∀ k : Fin (Module.finrank ℝ E),
      Real.sqrt (g.inner (expMap (I := I) g p (show TangentSpace I p from x))
        (radialJacobiField (I := I) g p x ((chartModelBasis E) k) 1)
        (radialJacobiField (I := I) g p x ((chartModelBasis E) k) 1)) ≤ B :=
  radialJacobi_fin_le_of_radius_deriv_at (I := I) g p x hK hb h1b
    (fun _ _ => hγ.contMDiffAt) hcard F hpar hON
    hFdiff hJdiff hDJdiff hODE
    hderivRadius hx hbasisSmall hbasis hmodel








omit [T2Space M] [SigmaCompactSpace M] in
theorem radialJacobi_one_le_of_scaled_radius_at
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E)
    {a r K b A B : ℝ} (ha : 0 < a) (hK : 0 ≤ K) (hb : 0 ≤ b)
    (h1b : (1 : ℝ) ≤ b)
    (hγ : ∀ t ∈ Icc (0 : ℝ) b,
      ContMDiffAt 𝓘(ℝ, ℝ) I 1 (radialCurve (I := I) g p x) t)
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (hcard : ∀ t : ℝ,
      Fintype.card ι = Module.finrank ℝ (TangentSpace I (radialCurve (I := I) g p x t)))
    (F : ι → ∀ t : ℝ, TangentSpace I (radialCurve (I := I) g p x t))
    (hpar : ∀ i, ∀ t ∈ Icc (0 : ℝ) b,
      covDerivAlong (I := I) g (radialCurve (I := I) g p x) (F i) t = 0)
    (hON : ∀ t ∈ Icc (0 : ℝ) b, ∀ i j,
      g.inner (radialCurve (I := I) g p x t) (F i t) (F j t) =
        if i = j then (1 : ℝ) else 0)
    (hFdiff : ∀ i, ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x) (F i) t) t)
    (hJdiff : ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x)
          (radialJacobiField (I := I) g p x (a • w)) t) t)
    (hDJdiff : ∀ t ∈ Icc (0 : ℝ) b, DifferentiableAt ℝ
      (chartRepAt (I := I) (radialCurve (I := I) g p x)
        (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (radialJacobiField (I := I) g p x (a • w)) s) t) t)
    (hODE : ∀ t ∈ Ico (0 : ℝ) b,
      g.inner (radialCurve (I := I) g p x t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x (a • w)) s) t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x (a • w)) s) t)
      ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
        (radialJacobiField (I := I) g p x (a • w) t)
        (radialJacobiField (I := I) g p x (a • w) t))
    (hderivRadius : ∀ x w : E, ‖x‖ < r → ‖w‖ < r →
      (covDerivAlong (I := I) g
        (fun v : ℝ => (expMap (I := I) g p (show TangentSpace I p from (v • x)) : M))
        (radialJacobiField (I := I) g p x w) 0 : E) = w)
    (hx : ‖x‖ < r) (hwsmall : ‖a • w‖ < r)
    (hinit : Real.sqrt (g.inner p (a • w) (a • w)) ≤ A)
    (hmodel :
      A + gronwallBound 0 (max K 1) (K * (b * A)) 1 ≤ a * B)
    (hxrad : ‖x‖ < expMapC2Radius (I := I) g p) :
    Real.sqrt (g.inner (expMap (I := I) g p (show TangentSpace I p from x))
      (radialJacobiField (I := I) g p x w 1)
      (radialJacobiField (I := I) g p x w 1)) ≤ B := by
  have hderiv :
      (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
        (radialJacobiField (I := I) g p x (a • w)) 0 : E) = a • w := by
    simpa [radialCurve] using hderivRadius x (a • w) hx hwsmall
  have hscaled :
      Real.sqrt (g.inner (expMap (I := I) g p (show TangentSpace I p from x))
        (radialJacobiField (I := I) g p x (a • w) 1)
        (radialJacobiField (I := I) g p x (a • w) 1)) ≤ a * B := by
    refine radialJacobi_one_le_at (I := I) g p x (a • w) hK hb h1b hγ hcard F hpar hON
      hFdiff hJdiff hDJdiff hODE ?_
    set vnorm : ℝ :=
      Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (radialJacobiField (I := I) g p x (a • w)) 0)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x (a • w)) 0))
    have hvA : vnorm ≤ A := by
      have hraw :
          Real.sqrt (g.inner (radialCurve (I := I) g p x 0)
              (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
                (radialJacobiField (I := I) g p x (a • w)) 0)
              (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
                (radialJacobiField (I := I) g p x (a • w)) 0)) ≤ A := by
        rw [radialCurve_zero (I := I) g p x]
        rw [hderiv]
        exact hinit
      simpa [vnorm] using hraw
    have heps :
        K * (b * vnorm) ≤ K * (b * A) := by
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hvA hb) hK
    have hmax : 0 ≤ max K 1 := le_max_of_le_right (by norm_num : (0 : ℝ) ≤ 1)
    have hgb :
        gronwallBound 0 (max K 1) (K * (b * vnorm)) 1 ≤
          gronwallBound 0 (max K 1) (K * (b * A)) 1 :=
      gronwallBound_zero_mono_eps hmax (by norm_num) heps
    calc
      vnorm + gronwallBound 0 (max K 1) (K * (b * vnorm)) 1
          ≤ A + gronwallBound 0 (max K 1) (K * (b * A)) 1 :=
            add_le_add hvA hgb
      _ ≤ a * B := hmodel
  exact radialJacobi_one_le_of_smul (I := I) g p x w ha hxrad hscaled








omit [T2Space M] [SigmaCompactSpace M] in
theorem radialJacobi_one_le_of_scaled_radius
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E)
    {a r K b A B : ℝ} (ha : 0 < a) (hK : 0 ≤ K) (hb : 0 ≤ b)
    (h1b : (1 : ℝ) ≤ b)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 (radialCurve (I := I) g p x))
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (hcard : ∀ t : ℝ,
      Fintype.card ι = Module.finrank ℝ (TangentSpace I (radialCurve (I := I) g p x t)))
    (F : ι → ∀ t : ℝ, TangentSpace I (radialCurve (I := I) g p x t))
    (hpar : ∀ i, ∀ t ∈ Icc (0 : ℝ) b,
      covDerivAlong (I := I) g (radialCurve (I := I) g p x) (F i) t = 0)
    (hON : ∀ t ∈ Icc (0 : ℝ) b, ∀ i j,
      g.inner (radialCurve (I := I) g p x t) (F i t) (F j t) =
        if i = j then (1 : ℝ) else 0)
    (hFdiff : ∀ i, ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x) (F i) t) t)
    (hJdiff : ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x)
          (radialJacobiField (I := I) g p x (a • w)) t) t)
    (hDJdiff : ∀ t ∈ Icc (0 : ℝ) b, DifferentiableAt ℝ
      (chartRepAt (I := I) (radialCurve (I := I) g p x)
        (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (radialJacobiField (I := I) g p x (a • w)) s) t) t)
    (hODE : ∀ t ∈ Ico (0 : ℝ) b,
      g.inner (radialCurve (I := I) g p x t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x (a • w)) s) t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x (a • w)) s) t)
      ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
        (radialJacobiField (I := I) g p x (a • w) t)
        (radialJacobiField (I := I) g p x (a • w) t))
    (hderivRadius : ∀ x w : E, ‖x‖ < r → ‖w‖ < r →
      (covDerivAlong (I := I) g
        (fun v : ℝ => (expMap (I := I) g p (show TangentSpace I p from (v • x)) : M))
        (radialJacobiField (I := I) g p x w) 0 : E) = w)
    (hx : ‖x‖ < r) (hwsmall : ‖a • w‖ < r)
    (hinit : Real.sqrt (g.inner p (a • w) (a • w)) ≤ A)
    (hmodel :
      A + gronwallBound 0 (max K 1) (K * (b * A)) 1 ≤ a * B)
    (hxrad : ‖x‖ < expMapC2Radius (I := I) g p) :
    Real.sqrt (g.inner (expMap (I := I) g p (show TangentSpace I p from x))
      (radialJacobiField (I := I) g p x w 1)
      (radialJacobiField (I := I) g p x w 1)) ≤ B :=
  radialJacobi_one_le_of_scaled_radius_at (I := I) g p x w ha hK hb h1b
    (fun _ _ => hγ.contMDiffAt) hcard F hpar hON hFdiff hJdiff hDJdiff hODE
    hderivRadius hx hwsmall hinit hmodel hxrad







omit [T2Space M] [SigmaCompactSpace M] in
theorem radialJacobi_one_ge_of_scaled_radius_at
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E)
    {a r K b B : ℝ} (ha : 0 < a) (hK : 0 ≤ K) (hb : 0 ≤ b)
    (h1b : (1 : ℝ) ≤ b)
    (hγ : ∀ t ∈ Icc (0 : ℝ) b,
      ContMDiffAt 𝓘(ℝ, ℝ) I 1 (radialCurve (I := I) g p x) t)
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (hcard : ∀ t : ℝ,
      Fintype.card ι = Module.finrank ℝ (TangentSpace I (radialCurve (I := I) g p x t)))
    (F : ι → ∀ t : ℝ, TangentSpace I (radialCurve (I := I) g p x t))
    (hpar : ∀ i, ∀ t ∈ Icc (0 : ℝ) b,
      covDerivAlong (I := I) g (radialCurve (I := I) g p x) (F i) t = 0)
    (hON : ∀ t ∈ Icc (0 : ℝ) b, ∀ i j,
      g.inner (radialCurve (I := I) g p x t) (F i t) (F j t) =
        if i = j then (1 : ℝ) else 0)
    (hFdiff : ∀ i, ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x) (F i) t) t)
    (hJdiff : ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x)
          (radialJacobiField (I := I) g p x (a • w)) t) t)
    (hDJdiff : ∀ t ∈ Icc (0 : ℝ) b, DifferentiableAt ℝ
      (chartRepAt (I := I) (radialCurve (I := I) g p x)
        (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (radialJacobiField (I := I) g p x (a • w)) s) t) t)
    (hODE : ∀ t ∈ Ico (0 : ℝ) b,
      g.inner (radialCurve (I := I) g p x t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x (a • w)) s) t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x (a • w)) s) t)
      ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
        (radialJacobiField (I := I) g p x (a • w) t)
        (radialJacobiField (I := I) g p x (a • w) t))
    (hderivRadius : ∀ x w : E, ‖x‖ < r → ‖w‖ < r →
      (covDerivAlong (I := I) g
        (fun v : ℝ => (expMap (I := I) g p (show TangentSpace I p from (v • x)) : M))
        (radialJacobiField (I := I) g p x w) 0 : E) = w)
    (hx : ‖x‖ < r) (hwsmall : ‖a • w‖ < r)
    (hmodel :
      a * B ≤ Real.sqrt (g.inner p (a • w) (a • w)) -
          gronwallBound 0 (max K 1)
            (K * (b * Real.sqrt (g.inner p (a • w) (a • w)))) 1)
    (hxrad : ‖x‖ < expMapC2Radius (I := I) g p) :
    B ≤ Real.sqrt (g.inner (expMap (I := I) g p (show TangentSpace I p from x))
      (radialJacobiField (I := I) g p x w 1)
      (radialJacobiField (I := I) g p x w 1)) := by
  have hderiv :
      (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
        (radialJacobiField (I := I) g p x (a • w)) 0 : E) = a • w := by
    simpa [radialCurve] using hderivRadius x (a • w) hx hwsmall
  have hscaled :
      a * B ≤ Real.sqrt (g.inner (expMap (I := I) g p (show TangentSpace I p from x))
        (radialJacobiField (I := I) g p x (a • w) 1)
        (radialJacobiField (I := I) g p x (a • w) 1)) := by
    refine radialJacobi_one_ge_at (I := I) g p x (a • w) hK hb h1b hγ hcard F hpar hON
      hFdiff hJdiff hDJdiff hODE ?_
    rw [radialCurve_zero (I := I) g p x]
    rw [hderiv]
    exact hmodel
  exact radialJacobi_one_ge_of_smul (I := I) g p x w ha hxrad hscaled







omit [T2Space M] [SigmaCompactSpace M] in
theorem radialJacobi_one_ge_of_scaled_radius
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E)
    {a r K b B : ℝ} (ha : 0 < a) (hK : 0 ≤ K) (hb : 0 ≤ b)
    (h1b : (1 : ℝ) ≤ b)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 (radialCurve (I := I) g p x))
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (hcard : ∀ t : ℝ,
      Fintype.card ι = Module.finrank ℝ (TangentSpace I (radialCurve (I := I) g p x t)))
    (F : ι → ∀ t : ℝ, TangentSpace I (radialCurve (I := I) g p x t))
    (hpar : ∀ i, ∀ t ∈ Icc (0 : ℝ) b,
      covDerivAlong (I := I) g (radialCurve (I := I) g p x) (F i) t = 0)
    (hON : ∀ t ∈ Icc (0 : ℝ) b, ∀ i j,
      g.inner (radialCurve (I := I) g p x t) (F i t) (F j t) =
        if i = j then (1 : ℝ) else 0)
    (hFdiff : ∀ i, ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x) (F i) t) t)
    (hJdiff : ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x)
          (radialJacobiField (I := I) g p x (a • w)) t) t)
    (hDJdiff : ∀ t ∈ Icc (0 : ℝ) b, DifferentiableAt ℝ
      (chartRepAt (I := I) (radialCurve (I := I) g p x)
        (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (radialJacobiField (I := I) g p x (a • w)) s) t) t)
    (hODE : ∀ t ∈ Ico (0 : ℝ) b,
      g.inner (radialCurve (I := I) g p x t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x (a • w)) s) t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x (a • w)) s) t)
      ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
        (radialJacobiField (I := I) g p x (a • w) t)
        (radialJacobiField (I := I) g p x (a • w) t))
    (hderivRadius : ∀ x w : E, ‖x‖ < r → ‖w‖ < r →
      (covDerivAlong (I := I) g
        (fun v : ℝ => (expMap (I := I) g p (show TangentSpace I p from (v • x)) : M))
        (radialJacobiField (I := I) g p x w) 0 : E) = w)
    (hx : ‖x‖ < r) (hwsmall : ‖a • w‖ < r)
    (hmodel :
      a * B ≤ Real.sqrt (g.inner p (a • w) (a • w)) -
          gronwallBound 0 (max K 1)
            (K * (b * Real.sqrt (g.inner p (a • w) (a • w)))) 1)
    (hxrad : ‖x‖ < expMapC2Radius (I := I) g p) :
    B ≤ Real.sqrt (g.inner (expMap (I := I) g p (show TangentSpace I p from x))
      (radialJacobiField (I := I) g p x w 1)
      (radialJacobiField (I := I) g p x w 1)) :=
  radialJacobi_one_ge_of_scaled_radius_at (I := I) g p x w ha hK hb h1b
    (fun _ _ => hγ.contMDiffAt) hcard F hpar hON hFdiff hJdiff hDJdiff hODE
    hderivRadius hx hwsmall hmodel hxrad








omit [T2Space M] [SigmaCompactSpace M] in
theorem radialJacobi_dir_ge_of_scaled_radius_at
    (g : SmoothRiemannianMetric I M) (p : M) (x : E)
    {a r K b B : ℝ} (ha : 0 < a) (hB_nonneg : 0 ≤ B)
    (hK : 0 ≤ K) (hb : 0 ≤ b) (h1b : (1 : ℝ) ≤ b)
    (hγ : ∀ t ∈ Icc (0 : ℝ) b,
      ContMDiffAt 𝓘(ℝ, ℝ) I 1 (radialCurve (I := I) g p x) t)
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (hcard : ∀ t : ℝ,
      Fintype.card ι = Module.finrank ℝ (TangentSpace I (radialCurve (I := I) g p x t)))
    (F : ι → ∀ t : ℝ, TangentSpace I (radialCurve (I := I) g p x t))
    (hpar : ∀ i, ∀ t ∈ Icc (0 : ℝ) b,
      covDerivAlong (I := I) g (radialCurve (I := I) g p x) (F i) t = 0)
    (hON : ∀ t ∈ Icc (0 : ℝ) b, ∀ i j,
      g.inner (radialCurve (I := I) g p x t) (F i t) (F j t) =
        if i = j then (1 : ℝ) else 0)
    (hFdiff : ∀ i, ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x) (F i) t) t)
    (hJdiff : ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
      ∀ t ∈ Icc (0 : ℝ) b,
        DifferentiableAt ℝ
          (chartRepAt (I := I) (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x
              (a • (∑ i, v i • (chartModelBasis E) i))) t) t)
    (hDJdiff : ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
      ∀ t ∈ Icc (0 : ℝ) b, DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x
              (a • (∑ i, v i • (chartModelBasis E) i))) s) t) t)
    (hODE : ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
      ∀ t ∈ Ico (0 : ℝ) b,
        g.inner (radialCurve (I := I) g p x t)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x
                (a • (∑ i, v i • (chartModelBasis E) i))) s) t)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x
                (a • (∑ i, v i • (chartModelBasis E) i))) s) t)
        ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
          (radialJacobiField (I := I) g p x
            (a • (∑ i, v i • (chartModelBasis E) i)) t)
          (radialJacobiField (I := I) g p x
            (a • (∑ i, v i • (chartModelBasis E) i)) t))
    (hderivRadius : ∀ x w : E, ‖x‖ < r → ‖w‖ < r →
      (covDerivAlong (I := I) g
        (fun v : ℝ => (expMap (I := I) g p (show TangentSpace I p from (v • x)) : M))
        (radialJacobiField (I := I) g p x w) 0 : E) = w)
    (hx : ‖x‖ < r)
    (hscaledSmall : ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
      ‖a • (∑ i, v i • (chartModelBasis E) i)‖ < r)
    (hmodel : ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
      a * B ≤ Real.sqrt
          (g.inner p (a • (∑ i, v i • (chartModelBasis E) i))
            (a • (∑ i, v i • (chartModelBasis E) i))) -
          gronwallBound 0 (max K 1)
            (K * (b * Real.sqrt
              (g.inner p (a • (∑ i, v i • (chartModelBasis E) i))
                (a • (∑ i, v i • (chartModelBasis E) i))))) 1)
    (hxrad : ‖x‖ < expMapC2Radius (I := I) g p) :
    ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
      B ^ 2 ≤ g.inner (expMap (I := I) g p (show TangentSpace I p from x))
        (radialJacobiField (I := I) g p x
          (∑ i, v i • (chartModelBasis E) i) 1)
        (radialJacobiField (I := I) g p x
          (∑ i, v i • (chartModelBasis E) i) 1) := by
  intro v hv
  set w : E := ∑ i, v i • (chartModelBasis E) i with hw
  have hsqrt :
      B ≤ Real.sqrt (g.inner (expMap (I := I) g p (show TangentSpace I p from x))
        (radialJacobiField (I := I) g p x w 1)
        (radialJacobiField (I := I) g p x w 1)) := by
    exact radialJacobi_one_ge_of_scaled_radius_at (I := I) g p x w ha hK hb h1b hγ
      hcard F hpar hON hFdiff (hJdiff v hv) (hDJdiff v hv) (hODE v hv)
      hderivRadius hx (by simpa [hw] using hscaledSmall v hv)
      (by simpa [hw] using hmodel v hv) hxrad
  set q := expMap (I := I) g p (show TangentSpace I p from x) with hq
  set J : TangentSpace I q := radialJacobiField (I := I) g p x w 1 with hJdef
  have hsq : B ^ 2 ≤ (Real.sqrt (g.inner q J J)) ^ 2 := by
    exact (sq_le_sq₀ hB_nonneg (Real.sqrt_nonneg _)).2 (by simpa [q, J] using hsqrt)
  have hJ_nonneg : 0 ≤ g.inner q J J := by
    rcases eq_or_ne J 0 with hJ | hJ
    · rw [hJ]
      have hzero :
          (g.inner q) (0 : TangentSpace I q) = (0 : TangentSpace I q →L[ℝ] ℝ) :=
        map_zero (g.inner q)
      rw [hzero]
      rfl
    · exact (g.pos q J hJ).le
  simpa [q, J, hw] using hsq.trans_eq (Real.sq_sqrt hJ_nonneg)








omit [T2Space M] [SigmaCompactSpace M] in
theorem radialJacobi_dir_ge_of_scaled_radius
    (g : SmoothRiemannianMetric I M) (p : M) (x : E)
    {a r K b B : ℝ} (ha : 0 < a) (hB_nonneg : 0 ≤ B)
    (hK : 0 ≤ K) (hb : 0 ≤ b) (h1b : (1 : ℝ) ≤ b)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 (radialCurve (I := I) g p x))
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (hcard : ∀ t : ℝ,
      Fintype.card ι = Module.finrank ℝ (TangentSpace I (radialCurve (I := I) g p x t)))
    (F : ι → ∀ t : ℝ, TangentSpace I (radialCurve (I := I) g p x t))
    (hpar : ∀ i, ∀ t ∈ Icc (0 : ℝ) b,
      covDerivAlong (I := I) g (radialCurve (I := I) g p x) (F i) t = 0)
    (hON : ∀ t ∈ Icc (0 : ℝ) b, ∀ i j,
      g.inner (radialCurve (I := I) g p x t) (F i t) (F j t) =
        if i = j then (1 : ℝ) else 0)
    (hFdiff : ∀ i, ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x) (F i) t) t)
    (hJdiff : ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
      ∀ t ∈ Icc (0 : ℝ) b,
        DifferentiableAt ℝ
          (chartRepAt (I := I) (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x
              (a • (∑ i, v i • (chartModelBasis E) i))) t) t)
    (hDJdiff : ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
      ∀ t ∈ Icc (0 : ℝ) b, DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x
              (a • (∑ i, v i • (chartModelBasis E) i))) s) t) t)
    (hODE : ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
      ∀ t ∈ Ico (0 : ℝ) b,
        g.inner (radialCurve (I := I) g p x t)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x
                (a • (∑ i, v i • (chartModelBasis E) i))) s) t)
          (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
              (radialJacobiField (I := I) g p x
                (a • (∑ i, v i • (chartModelBasis E) i))) s) t)
        ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
          (radialJacobiField (I := I) g p x
            (a • (∑ i, v i • (chartModelBasis E) i)) t)
          (radialJacobiField (I := I) g p x
            (a • (∑ i, v i • (chartModelBasis E) i)) t))
    (hderivRadius : ∀ x w : E, ‖x‖ < r → ‖w‖ < r →
      (covDerivAlong (I := I) g
        (fun v : ℝ => (expMap (I := I) g p (show TangentSpace I p from (v • x)) : M))
        (radialJacobiField (I := I) g p x w) 0 : E) = w)
    (hx : ‖x‖ < r)
    (hscaledSmall : ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
      ‖a • (∑ i, v i • (chartModelBasis E) i)‖ < r)
    (hmodel : ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
      a * B ≤ Real.sqrt
          (g.inner p (a • (∑ i, v i • (chartModelBasis E) i))
            (a • (∑ i, v i • (chartModelBasis E) i))) -
          gronwallBound 0 (max K 1)
            (K * (b * Real.sqrt
              (g.inner p (a • (∑ i, v i • (chartModelBasis E) i))
                (a • (∑ i, v i • (chartModelBasis E) i))))) 1)
    (hxrad : ‖x‖ < expMapC2Radius (I := I) g p) :
    ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
      B ^ 2 ≤ g.inner (expMap (I := I) g p (show TangentSpace I p from x))
        (radialJacobiField (I := I) g p x
          (∑ i, v i • (chartModelBasis E) i) 1)
        (radialJacobiField (I := I) g p x
          (∑ i, v i • (chartModelBasis E) i) 1) :=
  radialJacobi_dir_ge_of_scaled_radius_at (I := I) g p x ha hB_nonneg hK hb h1b
    (fun _ _ => hγ.contMDiffAt) hcard F hpar hON hFdiff hJdiff hDJdiff hODE
    hderivRadius hx hscaledSmall hmodel hxrad






omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
lemma model_ge_of_smul
    (g : SmoothRiemannianMetric I M) (p : M) (w : E)
    {a K b B : ℝ} (ha : 0 < a)
    (hmodel :
      B ≤ Real.sqrt (g.inner p w w) -
          gronwallBound 0 (max K 1)
            (K * (b * Real.sqrt (g.inner p w w))) 1) :
    a * B ≤ Real.sqrt (g.inner p (a • w) (a • w)) -
        gronwallBound 0 (max K 1)
          (K * (b * Real.sqrt (g.inner p (a • w) (a • w)))) 1 := by
  set s : ℝ := Real.sqrt (g.inner p w w) with hs
  have hsqrt :
      Real.sqrt (g.inner p (a • w) (a • w)) = a * s := by
    have hscale :
        g.inner p (a • w) (a • w) = a ^ 2 * g.inner p w w := by
      let v : TangentSpace I p := w
      have hscale_v : g.inner p (a • v) (a • v) = a ^ 2 * g.inner p v v := by
        rw [map_smul (g.inner p), ContinuousLinearMap.smul_apply,
          ContinuousLinearMap.map_smul, smul_eq_mul, smul_eq_mul]
        ring
      change g.inner p (a • v) (a • v) = a ^ 2 * g.inner p v v
      exact hscale_v
    rw [hscale, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq_eq_abs, abs_of_pos ha, hs]
  have herr :
      gronwallBound 0 (max K 1) (K * (b * (a * s))) 1 =
        a * gronwallBound 0 (max K 1) (K * (b * s)) 1 := by
    have heps : K * (b * (a * s)) = a * (K * (b * s)) := by ring
    rw [heps, gronwallBound_zero_mul_eps]
  rw [hsqrt, herr]
  have hmul := mul_le_mul_of_nonneg_left hmodel ha.le
  nlinarith


omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
lemma dirModel_ge_smul
    (g : SmoothRiemannianMetric I M) (p : M)
    {a K b B : ℝ} (ha : 0 < a)
    (hmodel : ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
      B ≤ Real.sqrt
          (g.inner p (∑ i, v i • (chartModelBasis E) i)
            (∑ i, v i • (chartModelBasis E) i)) -
          gronwallBound 0 (max K 1)
            (K * (b * Real.sqrt
              (g.inner p (∑ i, v i • (chartModelBasis E) i)
                (∑ i, v i • (chartModelBasis E) i)))) 1) :
    ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
      a * B ≤ Real.sqrt
          (g.inner p (a • (∑ i, v i • (chartModelBasis E) i))
            (a • (∑ i, v i • (chartModelBasis E) i))) -
          gronwallBound 0 (max K 1)
            (K * (b * Real.sqrt
              (g.inner p (a • (∑ i, v i • (chartModelBasis E) i))
                (a • (∑ i, v i • (chartModelBasis E) i))))) 1 := by
  intro v hv
  exact model_ge_of_smul (I := I) g p (∑ i, v i • (chartModelBasis E) i) ha
    (hmodel v hv)



omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
lemma dirModel_ge_of_bounds
    (g : SmoothRiemannianMetric I M) (p : M)
    {K b B₀ D B : ℝ} (hK : 0 ≤ K) (hb : 0 ≤ b)
    (hlo : ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
      B₀ ≤ Real.sqrt
        (g.inner p (∑ i, v i • (chartModelBasis E) i)
          (∑ i, v i • (chartModelBasis E) i)))
    (hhi : ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
      Real.sqrt
        (g.inner p (∑ i, v i • (chartModelBasis E) i)
          (∑ i, v i • (chartModelBasis E) i)) ≤ D)
    (hsmall :
      B ≤ B₀ - gronwallBound 0 (max K 1) (K * (b * D)) 1) :
    ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
      B ≤ Real.sqrt
          (g.inner p (∑ i, v i • (chartModelBasis E) i)
            (∑ i, v i • (chartModelBasis E) i)) -
          gronwallBound 0 (max K 1)
            (K * (b * Real.sqrt
              (g.inner p (∑ i, v i • (chartModelBasis E) i)
                (∑ i, v i • (chartModelBasis E) i)))) 1 := by
  intro v hv
  set s : ℝ := Real.sqrt
    (g.inner p (∑ i, v i • (chartModelBasis E) i)
      (∑ i, v i • (chartModelBasis E) i)) with hs
  have hslo : B₀ ≤ s := by
    simpa [s] using hlo v hv
  have hshi : s ≤ D := by
    simpa [s] using hhi v hv
  have heps : K * (b * s) ≤ K * (b * D) := by
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hshi hb) hK
  have hmax : 0 ≤ max K 1 := le_max_of_le_right (by norm_num : (0 : ℝ) ≤ 1)
  have hgb :
      gronwallBound 0 (max K 1) (K * (b * s)) 1 ≤
        gronwallBound 0 (max K 1) (K * (b * D)) 1 :=
    gronwallBound_zero_mono_eps hmax (by norm_num) heps
  nlinarith



omit [T2Space M] [SigmaCompactSpace M] in
omit [I.Boundaryless] [T2Space (TangentBundle I M)] in
lemma exists_dirModel_ge
    (g : SmoothRiemannianMetric I M) (p : M)
    {K : ℝ} (hK : 0 ≤ K) :
    ∃ b B : ℝ, 0 < b ∧ 0 < B ∧
      ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
        B ≤ Real.sqrt
            (g.inner p (∑ i, v i • (chartModelBasis E) i)
              (∑ i, v i • (chartModelBasis E) i)) -
            gronwallBound 0 (max K 1)
              (K * (b * Real.sqrt
                (g.inner p (∑ i, v i • (chartModelBasis E) i)
                  (∑ i, v i • (chartModelBasis E) i)))) 1 := by
  rcases exists_unitCoeff_bounds (I := I) g p with
    ⟨B₀, D, hB₀_pos, hD_nonneg, hlo, hhi⟩
  rcases exists_gron_small hB₀_pos hK hD_nonneg with ⟨b, B, hb_pos, hB_pos, hsmall⟩
  refine ⟨b, B, hb_pos, hB_pos, ?_⟩
  exact dirModel_ge_of_bounds (I := I) g p hK hb_pos.le hlo hhi hsmall



omit [T2Space M] [SigmaCompactSpace M] in
omit [I.Boundaryless] [T2Space (TangentBundle I M)] in
lemma exists_dirModel_ge1
    (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ K B : ℝ, 0 < K ∧ 0 < B ∧
      ∀ {k : ℝ}, 0 ≤ k → k ≤ K →
        ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
          B ≤ Real.sqrt
              (g.inner p (∑ i, v i • (chartModelBasis E) i)
                (∑ i, v i • (chartModelBasis E) i)) -
              gronwallBound 0 (max k 1)
                (k * Real.sqrt
                  (g.inner p (∑ i, v i • (chartModelBasis E) i)
                    (∑ i, v i • (chartModelBasis E) i))) 1 := by
  rcases exists_unitCoeff_bounds (I := I) g p with
    ⟨B₀, D, hB₀_pos, hD_nonneg, hlo, hhi⟩
  rcases exists_gron_smallK hB₀_pos hD_nonneg with ⟨K, B, hK_pos, hB_pos, hsmall⟩
  refine ⟨K, B, hK_pos, hB_pos, ?_⟩
  intro k hk_nonneg hk_le v hv
  set s : ℝ := Real.sqrt
    (g.inner p (∑ i, v i • (chartModelBasis E) i)
      (∑ i, v i • (chartModelBasis E) i)) with hs
  have hslo : B₀ ≤ s := by
    simpa [s] using hlo v hv
  have hshi : s ≤ D := by
    simpa [s] using hhi v hv
  have hsmall' :
      B ≤ B₀ - gronwallBound 0 (max k 1) (k * D) 1 :=
    hsmall hk_nonneg hk_le
  have heps : k * s ≤ k * D := mul_le_mul_of_nonneg_left hshi hk_nonneg
  have hmax : 0 ≤ max k 1 := le_max_of_le_right (by norm_num : (0 : ℝ) ≤ 1)
  have hgb :
      gronwallBound 0 (max k 1) (k * s) 1 ≤
        gronwallBound 0 (max k 1) (k * D) 1 :=
    gronwallBound_zero_mono_eps hmax (by norm_num) heps
  nlinarith






omit [T2Space M] [SigmaCompactSpace M] in
theorem radialJacobi_fin_le_of_scaled_radius_at
    (g : SmoothRiemannianMetric I M) (p : M) (x : E)
    {a r K b A B : ℝ} (ha : 0 < a) (hK : 0 ≤ K) (hb : 0 ≤ b)
    (h1b : (1 : ℝ) ≤ b)
    (hγ : ∀ t ∈ Icc (0 : ℝ) b,
      ContMDiffAt 𝓘(ℝ, ℝ) I 1 (radialCurve (I := I) g p x) t)
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (hcard : ∀ t : ℝ,
      Fintype.card ι = Module.finrank ℝ (TangentSpace I (radialCurve (I := I) g p x t)))
    (F : ι → ∀ t : ℝ, TangentSpace I (radialCurve (I := I) g p x t))
    (hpar : ∀ i, ∀ t ∈ Icc (0 : ℝ) b,
      covDerivAlong (I := I) g (radialCurve (I := I) g p x) (F i) t = 0)
    (hON : ∀ t ∈ Icc (0 : ℝ) b, ∀ i j,
      g.inner (radialCurve (I := I) g p x t) (F i t) (F j t) =
        if i = j then (1 : ℝ) else 0)
    (hFdiff : ∀ i, ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x) (F i) t) t)
    (hJdiff : ∀ k : Fin (Module.finrank ℝ E), ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x)
          (radialJacobiField (I := I) g p x (a • (chartModelBasis E) k)) t) t)
    (hDJdiff : ∀ k : Fin (Module.finrank ℝ E), ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x (a • (chartModelBasis E) k)) s) t) t)
    (hODE : ∀ k : Fin (Module.finrank ℝ E), ∀ t ∈ Ico (0 : ℝ) b,
      g.inner (radialCurve (I := I) g p x t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x (a • (chartModelBasis E) k)) s) t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x (a • (chartModelBasis E) k)) s) t)
      ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
        (radialJacobiField (I := I) g p x (a • (chartModelBasis E) k) t)
        (radialJacobiField (I := I) g p x (a • (chartModelBasis E) k) t))
    (hderivRadius : ∀ x w : E, ‖x‖ < r → ‖w‖ < r →
      (covDerivAlong (I := I) g
        (fun v : ℝ => (expMap (I := I) g p (show TangentSpace I p from (v • x)) : M))
        (radialJacobiField (I := I) g p x w) 0 : E) = w)
    (hx : ‖x‖ < r)
    (hscaledSmall : ∀ k : Fin (Module.finrank ℝ E), ‖a • (chartModelBasis E) k‖ < r)
    (hinit : ∀ k : Fin (Module.finrank ℝ E),
      Real.sqrt (g.inner p (a • (chartModelBasis E) k) (a • (chartModelBasis E) k)) ≤ A)
    (hmodel :
      A + gronwallBound 0 (max K 1) (K * (b * A)) 1 ≤ a * B)
    (hxrad : ‖x‖ < expMapC2Radius (I := I) g p) :
    ∀ k : Fin (Module.finrank ℝ E),
      Real.sqrt (g.inner (expMap (I := I) g p (show TangentSpace I p from x))
        (radialJacobiField (I := I) g p x ((chartModelBasis E) k) 1)
        (radialJacobiField (I := I) g p x ((chartModelBasis E) k) 1)) ≤ B := by
  intro k
  exact radialJacobi_one_le_of_scaled_radius_at (I := I) g p x ((chartModelBasis E) k)
    ha hK hb h1b hγ hcard F hpar hON hFdiff (hJdiff k) (hDJdiff k) (hODE k)
    hderivRadius hx (hscaledSmall k) (hinit k) hmodel hxrad






omit [T2Space M] [SigmaCompactSpace M] in
theorem radialJacobi_fin_le_of_scaled_radius
    (g : SmoothRiemannianMetric I M) (p : M) (x : E)
    {a r K b A B : ℝ} (ha : 0 < a) (hK : 0 ≤ K) (hb : 0 ≤ b)
    (h1b : (1 : ℝ) ≤ b)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 (radialCurve (I := I) g p x))
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (hcard : ∀ t : ℝ,
      Fintype.card ι = Module.finrank ℝ (TangentSpace I (radialCurve (I := I) g p x t)))
    (F : ι → ∀ t : ℝ, TangentSpace I (radialCurve (I := I) g p x t))
    (hpar : ∀ i, ∀ t ∈ Icc (0 : ℝ) b,
      covDerivAlong (I := I) g (radialCurve (I := I) g p x) (F i) t = 0)
    (hON : ∀ t ∈ Icc (0 : ℝ) b, ∀ i j,
      g.inner (radialCurve (I := I) g p x t) (F i t) (F j t) =
        if i = j then (1 : ℝ) else 0)
    (hFdiff : ∀ i, ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x) (F i) t) t)
    (hJdiff : ∀ k : Fin (Module.finrank ℝ E), ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x)
          (radialJacobiField (I := I) g p x (a • (chartModelBasis E) k)) t) t)
    (hDJdiff : ∀ k : Fin (Module.finrank ℝ E), ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x (a • (chartModelBasis E) k)) s) t) t)
    (hODE : ∀ k : Fin (Module.finrank ℝ E), ∀ t ∈ Ico (0 : ℝ) b,
      g.inner (radialCurve (I := I) g p x t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x (a • (chartModelBasis E) k)) s) t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x (a • (chartModelBasis E) k)) s) t)
      ≤ K ^ 2 * g.inner (radialCurve (I := I) g p x t)
        (radialJacobiField (I := I) g p x (a • (chartModelBasis E) k) t)
        (radialJacobiField (I := I) g p x (a • (chartModelBasis E) k) t))
    (hderivRadius : ∀ x w : E, ‖x‖ < r → ‖w‖ < r →
      (covDerivAlong (I := I) g
        (fun v : ℝ => (expMap (I := I) g p (show TangentSpace I p from (v • x)) : M))
        (radialJacobiField (I := I) g p x w) 0 : E) = w)
    (hx : ‖x‖ < r)
    (hscaledSmall : ∀ k : Fin (Module.finrank ℝ E), ‖a • (chartModelBasis E) k‖ < r)
    (hinit : ∀ k : Fin (Module.finrank ℝ E),
      Real.sqrt (g.inner p (a • (chartModelBasis E) k) (a • (chartModelBasis E) k)) ≤ A)
    (hmodel :
      A + gronwallBound 0 (max K 1) (K * (b * A)) 1 ≤ a * B)
    (hxrad : ‖x‖ < expMapC2Radius (I := I) g p) :
    ∀ k : Fin (Module.finrank ℝ E),
      Real.sqrt (g.inner (expMap (I := I) g p (show TangentSpace I p from x))
        (radialJacobiField (I := I) g p x ((chartModelBasis E) k) 1)
        (radialJacobiField (I := I) g p x ((chartModelBasis E) k) 1)) ≤ B :=
  radialJacobi_fin_le_of_scaled_radius_at (I := I) g p x ha hK hb h1b
    (fun _ _ => hγ.contMDiffAt) hcard F hpar hON hFdiff hJdiff hDJdiff hODE
    hderivRadius hx hscaledSmall hinit hmodel hxrad

open Bundle in
attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in


theorem exists_fin_le_rm04_at
    [PseudoEMetricSpace M] [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    ∃ r : Real, 0 < r ∧ ∀ x : E, ‖x‖ < r →
      ∀ {a K R Vb b A B : ℝ}, 0 < a → 0 ≤ K → 0 ≤ Vb → 0 ≤ b → b ≤ 1 →
      (1 : ℝ) ≤ b →
      (∀ k : Fin (Module.finrank ℝ E), ‖a • (chartModelBasis E) k‖ < r) →
      Real.sqrt (g.inner p x x) ≤ Vb →
      Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          R * Vb ^ 2 ≤ K →
      (∀ t (_ht : t ∈ Ioo (0 : Real) b),
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (radialCurve (I := I) g p x t) 4
          (DifferentialGeometry.Integral.Connection.metricRm04At
            (I := I) (M := M) g (radialCurve (I := I) g p x t))) ≤ R) →
      (∀ t ∈ Icc (0 : ℝ) b,
        ContMDiffAt 𝓘(ℝ, ℝ) I 1 (radialCurve (I := I) g p x) t) →
      ∀ {ι : Type*}, [Fintype ι] → [DecidableEq ι] → [Nonempty ι] →
      (∀ t : ℝ,
        Fintype.card ι = Module.finrank ℝ (TangentSpace I (radialCurve (I := I) g p x t))) →
      (F : ι → ∀ t : ℝ, TangentSpace I (radialCurve (I := I) g p x t)) →
      (∀ i, ∀ t ∈ Icc (0 : ℝ) b,
        covDerivAlong (I := I) g (radialCurve (I := I) g p x) (F i) t = 0) →
      (∀ t ∈ Icc (0 : ℝ) b, ∀ i j,
        g.inner (radialCurve (I := I) g p x t) (F i t) (F j t) =
          if i = j then (1 : ℝ) else 0) →
      (∀ i, ∀ t ∈ Icc (0 : ℝ) b,
        DifferentiableAt ℝ
          (chartRepAt (I := I) (radialCurve (I := I) g p x) (F i) t) t) →
      (∀ k : Fin (Module.finrank ℝ E),
        Real.sqrt (g.inner p (a • (chartModelBasis E) k) (a • (chartModelBasis E) k)) ≤ A) →
      A + gronwallBound 0 (max K 1) (K * (b * A)) 1 ≤ a * B →
      ‖x‖ < expMapC2Radius (I := I) g p →
      ∀ k : Fin (Module.finrank ℝ E),
        Real.sqrt (g.inner (expMap (I := I) g p (show TangentSpace I p from x))
          (radialJacobiField (I := I) g p x ((chartModelBasis E) k) 1)
          (radialJacobiField (I := I) g p x ((chartModelBasis E) k) 1)) ≤ B := by
  obtain ⟨r, hr, hdata, hderiv⟩ := exists_rm04_pack (I := I) g hEnorm p
  refine ⟨r, hr, ?_⟩
  intro x hx a K R Vb b A B ha hK hVb hb0 hb1 h1b hsmall hlaunch hKbound hRm
    hγ ι _ _ _ hcard F hpar hON hFdiff hinit hmodel hxrad
  letI : Fintype ι := ‹Fintype ι›
  letI : DecidableEq ι := ‹DecidableEq ι›
  letI : Nonempty ι := ‹Nonempty ι›
  obtain ⟨hJdiff, hDJdiff, hODE⟩ :=
    hdata x hx hK hVb hb1 hsmall hlaunch hKbound hRm
  exact radialJacobi_fin_le_of_scaled_radius_at (I := I) g p x ha hK hb0 h1b hγ
    hcard F hpar hON hFdiff hJdiff hDJdiff hODE hderiv hx hsmall hinit hmodel hxrad

open Bundle in
attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in


theorem exists_fin_le_rm04
    [PseudoEMetricSpace M] [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    ∃ r : Real, 0 < r ∧ ∀ x : E, ‖x‖ < r →
      ∀ {a K R Vb b A B : ℝ}, 0 < a → 0 ≤ K → 0 ≤ Vb → 0 ≤ b → b ≤ 1 →
      (1 : ℝ) ≤ b →
      (∀ k : Fin (Module.finrank ℝ E), ‖a • (chartModelBasis E) k‖ < r) →
      Real.sqrt (g.inner p x x) ≤ Vb →
      Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          R * Vb ^ 2 ≤ K →
      (∀ t (_ht : t ∈ Ioo (0 : Real) b),
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (radialCurve (I := I) g p x t) 4
          (DifferentialGeometry.Integral.Connection.metricRm04At
            (I := I) (M := M) g (radialCurve (I := I) g p x t))) ≤ R) →
      ContMDiff 𝓘(ℝ, ℝ) I 1 (radialCurve (I := I) g p x) →
      ∀ {ι : Type*}, [Fintype ι] → [DecidableEq ι] → [Nonempty ι] →
      (∀ t : ℝ,
        Fintype.card ι = Module.finrank ℝ (TangentSpace I (radialCurve (I := I) g p x t))) →
      (F : ι → ∀ t : ℝ, TangentSpace I (radialCurve (I := I) g p x t)) →
      (∀ i, ∀ t ∈ Icc (0 : ℝ) b,
        covDerivAlong (I := I) g (radialCurve (I := I) g p x) (F i) t = 0) →
      (∀ t ∈ Icc (0 : ℝ) b, ∀ i j,
        g.inner (radialCurve (I := I) g p x t) (F i t) (F j t) =
          if i = j then (1 : ℝ) else 0) →
      (∀ i, ∀ t ∈ Icc (0 : ℝ) b,
        DifferentiableAt ℝ
          (chartRepAt (I := I) (radialCurve (I := I) g p x) (F i) t) t) →
      (∀ k : Fin (Module.finrank ℝ E),
        Real.sqrt (g.inner p (a • (chartModelBasis E) k) (a • (chartModelBasis E) k)) ≤ A) →
      A + gronwallBound 0 (max K 1) (K * (b * A)) 1 ≤ a * B →
      ‖x‖ < expMapC2Radius (I := I) g p →
      ∀ k : Fin (Module.finrank ℝ E),
        Real.sqrt (g.inner (expMap (I := I) g p (show TangentSpace I p from x))
          (radialJacobiField (I := I) g p x ((chartModelBasis E) k) 1)
          (radialJacobiField (I := I) g p x ((chartModelBasis E) k) 1)) ≤ B := by
  obtain ⟨r, hr, h⟩ := exists_fin_le_rm04_at (I := I) g hEnorm p
  refine ⟨r, hr, ?_⟩
  intro x hx a K R Vb b A B ha hK hVb hb0 hb1 h1b hsmall hlaunch hKbound hRm
    hγ ι _ _ _ hcard F hpar hON hFdiff hinit hmodel hxrad
  exact h x hx ha hK hVb hb0 hb1 h1b hsmall hlaunch hKbound hRm
    (fun _ _ => hγ.contMDiffAt) hcard F hpar hON hFdiff hinit hmodel hxrad

open Bundle in
attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in


theorem exists_dir_ge_rm04_at
    [PseudoEMetricSpace M] [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    ∃ r : Real, 0 < r ∧ ∀ x : E, ‖x‖ < r →
      ∀ {a K R Vb b B : ℝ}, 0 < a → 0 ≤ B → 0 ≤ K → 0 ≤ Vb → 0 ≤ b →
      b ≤ 1 → (1 : ℝ) ≤ b →
      (∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
        ‖a • (∑ i, v i • (chartModelBasis E) i)‖ < r) →
      Real.sqrt (g.inner p x x) ≤ Vb →
      Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          R * Vb ^ 2 ≤ K →
      (∀ t (_ht : t ∈ Ioo (0 : Real) b),
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (radialCurve (I := I) g p x t) 4
          (DifferentialGeometry.Integral.Connection.metricRm04At
            (I := I) (M := M) g (radialCurve (I := I) g p x t))) ≤ R) →
      (∀ t ∈ Icc (0 : ℝ) b,
        ContMDiffAt 𝓘(ℝ, ℝ) I 1 (radialCurve (I := I) g p x) t) →
      ∀ {ι : Type*}, [Fintype ι] → [DecidableEq ι] → [Nonempty ι] →
      (∀ t : ℝ,
        Fintype.card ι = Module.finrank ℝ (TangentSpace I (radialCurve (I := I) g p x t))) →
      (F : ι → ∀ t : ℝ, TangentSpace I (radialCurve (I := I) g p x t)) →
      (∀ i, ∀ t ∈ Icc (0 : ℝ) b,
        covDerivAlong (I := I) g (radialCurve (I := I) g p x) (F i) t = 0) →
      (∀ t ∈ Icc (0 : ℝ) b, ∀ i j,
        g.inner (radialCurve (I := I) g p x t) (F i t) (F j t) =
          if i = j then (1 : ℝ) else 0) →
      (∀ i, ∀ t ∈ Icc (0 : ℝ) b,
        DifferentiableAt ℝ
          (chartRepAt (I := I) (radialCurve (I := I) g p x) (F i) t) t) →
      (∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
        a * B ≤ Real.sqrt
            (g.inner p (a • (∑ i, v i • (chartModelBasis E) i))
              (a • (∑ i, v i • (chartModelBasis E) i))) -
            gronwallBound 0 (max K 1)
              (K * (b * Real.sqrt
                (g.inner p (a • (∑ i, v i • (chartModelBasis E) i))
                  (a • (∑ i, v i • (chartModelBasis E) i))))) 1) →
      ‖x‖ < expMapC2Radius (I := I) g p →
      ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
        B ^ 2 ≤ g.inner (expMap (I := I) g p (show TangentSpace I p from x))
          (radialJacobiField (I := I) g p x
            (∑ i, v i • (chartModelBasis E) i) 1)
          (radialJacobiField (I := I) g p x
            (∑ i, v i • (chartModelBasis E) i) 1) := by
  obtain ⟨r₀, hr₀, hdata⟩ := exists_rm04_data (I := I) g hEnorm p
  obtain ⟨r₁, hr₁, hderiv⟩ := exists_radialJacobi_deriv_radius (I := I) g p
  refine ⟨min r₀ r₁, lt_min hr₀ hr₁, ?_⟩
  intro x hx a K R Vb b B ha hB hK hVb hb0 hb1 h1b hsmall hlaunch hKbound hRm
    hγ ι _ _ _ hcard F hpar hON hFdiff hmodel hxrad
  letI : Fintype ι := ‹Fintype ι›
  letI : DecidableEq ι := ‹DecidableEq ι›
  letI : Nonempty ι := ‹Nonempty ι›
  have hx₀ : ‖x‖ < r₀ := lt_of_lt_of_le hx (min_le_left _ _)
  have hx₁ : ‖x‖ < r₁ := lt_of_lt_of_le hx (min_le_right _ _)
  have hderiv' : ∀ x w : E, ‖x‖ < min r₀ r₁ → ‖w‖ < min r₀ r₁ →
      (covDerivAlong (I := I) g
        (fun v : ℝ => (expMap (I := I) g p (show TangentSpace I p from (v • x)) : M))
        (radialJacobiField (I := I) g p x w) 0 : E) = w := by
    intro y z hy hz
    exact hderiv y z (lt_of_lt_of_le hy (min_le_right _ _))
      (lt_of_lt_of_le hz (min_le_right _ _))
  refine radialJacobi_dir_ge_of_scaled_radius_at (I := I) g p x ha hB hK hb0 h1b hγ
    hcard F hpar hON hFdiff ?_ ?_ ?_ hderiv' hx hsmall hmodel hxrad
  · intro v hv
    exact (hdata x (a • (∑ i, v i • (chartModelBasis E) i)) hx₀
      (lt_of_lt_of_le (hsmall v hv) (min_le_left _ _))
      hK hVb hb1 hlaunch hKbound hRm).1
  · intro v hv
    exact (hdata x (a • (∑ i, v i • (chartModelBasis E) i)) hx₀
      (lt_of_lt_of_le (hsmall v hv) (min_le_left _ _))
      hK hVb hb1 hlaunch hKbound hRm).2.1
  · intro v hv
    exact (hdata x (a • (∑ i, v i • (chartModelBasis E) i)) hx₀
      (lt_of_lt_of_le (hsmall v hv) (min_le_left _ _))
      hK hVb hb1 hlaunch hKbound hRm).2.2

open Bundle in
attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in


theorem exists_dir_ge_rm04
    [PseudoEMetricSpace M] [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M] [ConnectedSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    ∃ r : Real, 0 < r ∧ ∀ x : E, ‖x‖ < r →
      ∀ {a K R Vb b B : ℝ}, 0 < a → 0 ≤ B → 0 ≤ K → 0 ≤ Vb → 0 ≤ b →
      b ≤ 1 → (1 : ℝ) ≤ b →
      (∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
        ‖a • (∑ i, v i • (chartModelBasis E) i)‖ < r) →
      Real.sqrt (g.inner p x x) ≤ Vb →
      Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank ℝ E)) : Real)) *
          R * Vb ^ 2 ≤ K →
      (∀ t (_ht : t ∈ Ioo (0 : Real) b),
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (radialCurve (I := I) g p x t) 4
          (DifferentialGeometry.Integral.Connection.metricRm04At
            (I := I) (M := M) g (radialCurve (I := I) g p x t))) ≤ R) →
      ContMDiff 𝓘(ℝ, ℝ) I 1 (radialCurve (I := I) g p x) →
      ∀ {ι : Type*}, [Fintype ι] → [DecidableEq ι] → [Nonempty ι] →
      (∀ t : ℝ,
        Fintype.card ι = Module.finrank ℝ (TangentSpace I (radialCurve (I := I) g p x t))) →
      (F : ι → ∀ t : ℝ, TangentSpace I (radialCurve (I := I) g p x t)) →
      (∀ i, ∀ t ∈ Icc (0 : ℝ) b,
        covDerivAlong (I := I) g (radialCurve (I := I) g p x) (F i) t = 0) →
      (∀ t ∈ Icc (0 : ℝ) b, ∀ i j,
        g.inner (radialCurve (I := I) g p x t) (F i t) (F j t) =
          if i = j then (1 : ℝ) else 0) →
      (∀ i, ∀ t ∈ Icc (0 : ℝ) b,
        DifferentiableAt ℝ
          (chartRepAt (I := I) (radialCurve (I := I) g p x) (F i) t) t) →
      (∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
        a * B ≤ Real.sqrt
            (g.inner p (a • (∑ i, v i • (chartModelBasis E) i))
              (a • (∑ i, v i • (chartModelBasis E) i))) -
            gronwallBound 0 (max K 1)
              (K * (b * Real.sqrt
                (g.inner p (a • (∑ i, v i • (chartModelBasis E) i))
                  (a • (∑ i, v i • (chartModelBasis E) i))))) 1) →
      ‖x‖ < expMapC2Radius (I := I) g p →
      ∀ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖v‖ = 1 →
        B ^ 2 ≤ g.inner (expMap (I := I) g p (show TangentSpace I p from x))
          (radialJacobiField (I := I) g p x
            (∑ i, v i • (chartModelBasis E) i) 1)
          (radialJacobiField (I := I) g p x
            (∑ i, v i • (chartModelBasis E) i) 1) := by
  obtain ⟨r, hr, h⟩ := exists_dir_ge_rm04_at (I := I) g hEnorm p
  refine ⟨r, hr, ?_⟩
  intro x hx a K R Vb b B ha hB hK hVb hb0 hb1 h1b hsmall hlaunch hKbound hRm
    hγ ι _ _ _ hcard F hpar hON hFdiff hmodel hxrad
  exact h x hx ha hB hK hVb hb0 hb1 h1b hsmall hlaunch hKbound hRm
    (fun _ _ => hγ.contMDiffAt) hcard F hpar hON hFdiff hmodel hxrad

end Radial

end VolumeComparison
end Riemannian
end Geometry
end DifferentialGeometry
