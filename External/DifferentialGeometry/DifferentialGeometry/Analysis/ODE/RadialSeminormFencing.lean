import DifferentialGeometry.Geometry.Exponential.Defs
import DifferentialGeometry.Geometry.Exponential.Smoothness.MfderivZero
import DifferentialGeometry.Geometry.Exponential.Smoothness.OffZero
import DifferentialGeometry.Geometry.Comparison.NormalCoordinates
import DifferentialGeometry.Geometry.Comparison.InjectivityRadius
import DifferentialGeometry.Geometry.Geodesic.Equation
import DifferentialGeometry.Geometry.Geodesic.Uniqueness
import DifferentialGeometry.Geometry.Geodesic.MaximalInterval
import DifferentialGeometry.Geometry.Geodesic.CrossVFReduction
import DifferentialGeometry.Geometry.Exponential.ChartFlow.SmallVelocityRescaling
import DifferentialGeometry.Geometry.Exponential.ChartFlow.RescaledLift
import DifferentialGeometry.Geometry.Exponential.ChartFlow.UniformExistence
import DifferentialGeometry.Analysis.Integration.Measure.ChartDensity
import DifferentialGeometry.Geometry.Comparison.Variation.SecondVariation
import Mathlib.Geometry.Manifold.Riemannian.PathELength


noncomputable section

open Set Function Filter Bundle Manifold
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

section RadialLengthAnalyticEngine

open MeasureTheory intervalIntegral

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

private lemma psd_cauchy_schwarz (B : F →L[ℝ] F →L[ℝ] ℝ)
    (hsym : ∀ x y, B x y = B y x) (hnn : ∀ x, 0 ≤ B x x) (x y : F) :
    (B x y) ^ 2 ≤ B x x * B y y := by
  by_cases hy : B y y = 0
  · have key : ∀ t : ℝ, 0 ≤ B x x - 2 * t * B x y := by
      intro t
      have h := hnn (x - t • y)
      have expand : B (x - t • y) (x - t • y) = B x x - 2 * t * B x y + t ^ 2 * B y y := by
        simp only [map_sub, map_smul, ContinuousLinearMap.sub_apply,
          ContinuousLinearMap.smul_apply, smul_eq_mul]
        rw [hsym y x]; ring
      rw [expand, hy] at h; linarith [h]
    rw [hy, mul_zero]
    by_contra hcon
    rw [not_le] at hcon
    have hxy : B x y ≠ 0 := by intro h0; rw [h0] at hcon; norm_num at hcon
    have h2 : 2 * ((B x x + 1) / (2 * B x y)) * B x y = B x x + 1 := by field_simp
    have := key ((B x x + 1) / (2 * B x y))
    rw [h2] at this; linarith
  · have hpos : 0 < B y y := lt_of_le_of_ne (hnn y) (Ne.symm hy)
    have h := hnn (x - (B x y / B y y) • y)
    have expand : B (x - (B x y / B y y) • y) (x - (B x y / B y y) • y)
        = B x x - (B x y) ^ 2 / B y y := by
      simp only [map_sub, map_smul, ContinuousLinearMap.sub_apply,
        ContinuousLinearMap.smul_apply, smul_eq_mul]
      rw [hsym y x]; field_simp; ring
    rw [expand] at h
    have hb : (B x y) ^ 2 / B y y ≤ B x x := by linarith
    have := (div_le_iff₀ hpos).mp hb
    linarith [this]

private lemma psd_seminorm_triangle (B : F →L[ℝ] F →L[ℝ] ℝ)
    (hsym : ∀ x y, B x y = B y x) (hnn : ∀ x, 0 ≤ B x x) (x y : F) :
    Real.sqrt (B (x + y) (x + y)) ≤ Real.sqrt (B x x) + Real.sqrt (B y y) := by
  have hxx := hnn x; have hyy := hnn y
  have hcs := psd_cauchy_schwarz B hsym hnn x y
  have hexp : B (x + y) (x + y) = B x x + 2 * B x y + B y y := by
    simp only [map_add, ContinuousLinearMap.add_apply]; rw [hsym y x]; ring
  have hbxy_le : B x y ≤ Real.sqrt (B x x) * Real.sqrt (B y y) := by
    have h1 : B x y ≤ |B x y| := le_abs_self _
    have h2 : |B x y| ≤ Real.sqrt (B x x) * Real.sqrt (B y y) := by
      rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul hxx]
      exact Real.sqrt_le_sqrt hcs
    linarith
  have hrhs : (Real.sqrt (B x x) + Real.sqrt (B y y)) ^ 2
      = B x x + 2 * (Real.sqrt (B x x) * Real.sqrt (B y y)) + B y y := by
    rw [add_sq, Real.sq_sqrt hxx, Real.sq_sqrt hyy]; ring
  have hle : B (x + y) (x + y) ≤ (Real.sqrt (B x x) + Real.sqrt (B y y)) ^ 2 := by
    rw [hexp, hrhs]; linarith
  calc Real.sqrt (B (x + y) (x + y))
        ≤ Real.sqrt ((Real.sqrt (B x x) + Real.sqrt (B y y)) ^ 2) := Real.sqrt_le_sqrt hle
    _ = Real.sqrt (B x x) + Real.sqrt (B y y) := by rw [Real.sqrt_sq (by positivity)]

private lemma psd_reverse_triangle (B : F →L[ℝ] F →L[ℝ] ℝ)
    (hsym : ∀ x y, B x y = B y x) (hnn : ∀ x, 0 ≤ B x x) (x y : F) :
    |Real.sqrt (B x x) - Real.sqrt (B y y)| ≤ Real.sqrt (B (x - y) (x - y)) := by
  have h1 : Real.sqrt (B x x) ≤ Real.sqrt (B (x - y) (x - y)) + Real.sqrt (B y y) := by
    have := psd_seminorm_triangle B hsym hnn (x - y) y
    rwa [sub_add_cancel] at this
  have h2 : Real.sqrt (B y y) ≤ Real.sqrt (B (y - x) (y - x)) + Real.sqrt (B x x) := by
    have := psd_seminorm_triangle B hsym hnn (y - x) x
    rwa [sub_add_cancel] at this
  have hsymq : B (y - x) (y - x) = B (x - y) (x - y) := by
    have hyx : y - x = -(x - y) := by abel
    rw [hyx]
    simp only [map_neg, ContinuousLinearMap.neg_apply, neg_neg]
  rw [hsymq] at h2
  rw [abs_sub_le_iff]; constructor <;> linarith

lemma psd_sqrt_lipschitz (B : F →L[ℝ] F →L[ℝ] ℝ)
    (hsym : ∀ x y, B x y = B y x) (hnn : ∀ x, 0 ≤ B x x) :
    LipschitzWith (Real.toNNReal (Real.sqrt ‖B‖)) (fun x => Real.sqrt (B x x)) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  rw [Real.dist_eq, Real.coe_toNNReal _ (Real.sqrt_nonneg _), dist_eq_norm]
  have hb0 : (0 : ℝ) ≤ ‖B‖ := by positivity
  calc |Real.sqrt (B x x) - Real.sqrt (B y y)|
        ≤ Real.sqrt (B (x - y) (x - y)) := psd_reverse_triangle B hsym hnn x y
    _ ≤ Real.sqrt ‖B‖ * ‖x - y‖ := by
        have hbz : B (x - y) (x - y) ≤ ‖B‖ * (‖x - y‖ * ‖x - y‖) := by
          calc B (x - y) (x - y) ≤ ‖B (x - y) (x - y)‖ := le_abs_self _
            _ ≤ ‖B‖ * ‖x - y‖ * ‖x - y‖ := B.le_opNorm₂ (x - y) (x - y)
            _ = ‖B‖ * (‖x - y‖ * ‖x - y‖) := by ring
        calc Real.sqrt (B (x - y) (x - y))
              ≤ Real.sqrt (‖B‖ * (‖x - y‖ * ‖x - y‖)) := Real.sqrt_le_sqrt hbz
          _ = Real.sqrt ‖B‖ * ‖x - y‖ := by
              rw [Real.sqrt_mul hb0, show ‖x - y‖ * ‖x - y‖ = ‖x - y‖ ^ 2 by ring,
                Real.sqrt_sq (norm_nonneg _)]

lemma angular_hasDerivAt_zero (B : F →L[ℝ] F →L[ℝ] ℝ)
    {c : ℝ → F} {c' : F} {ρ : ℝ → ℝ} {t : ℝ}
    (hc : HasDerivAt c c' t) (hρt : 0 < ρ t)
    (hρ : HasDerivAt ρ (B (c t) c' / ρ t) t)
    (hρsq : ρ t ^ 2 = B (c t) (c t))
    (hrad : c' = (B (c t) c' / B (c t) (c t)) • c t) :
    HasDerivAt (fun s => (ρ s)⁻¹ • c s) 0 t := by
  have hrne : ρ t ≠ 0 := ne_of_gt hρt
  have hBne : B (c t) (c t) ≠ 0 := by rw [← hρsq]; positivity
  set k : ℝ := B (c t) c' with hk_def
  have hinv : HasDerivAt (fun s => (ρ s)⁻¹) (-(k / ρ t) / (ρ t)^2) t := by
    have h := hρ.inv hrne
    simpa [hk_def] using h
  have hθ' : HasDerivAt (fun s => (ρ s)⁻¹ • c s)
      ((ρ t)⁻¹ • c' + (-(k / ρ t) / (ρ t)^2) • c t) t := by
    have h := hinv.smul hc
    simpa using h
  have hzero : (ρ t)⁻¹ • c' + (-(k / ρ t) / (ρ t)^2) • c t = 0 := by
    rw [hrad]
    rw [smul_smul, ← add_smul]
    rw [show (ρ t)⁻¹ * (k / B (c t) (c t)) + -(k / ρ t) / ρ t ^ 2 = 0 by
      rw [← hρsq]; field_simp; ring]
    rw [zero_smul]
  rwa [hzero] at hθ'

lemma image_radialDist_le_intervalIntegral_of_slope_le
    {ρ φ : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hρc : ContinuousOn ρ (Set.Icc a b)) (hρa : ρ a ≤ 0)
    (hφint : MeasureTheory.IntegrableOn φ (Set.Icc a b) MeasureTheory.volume)
    (hφcont : ∀ x ∈ Set.Ico a b, ContinuousWithinAt φ (Set.Ioi x) x)
    (hslope : ∀ x ∈ Set.Ico a b, ∀ r, φ x < r →
      ∃ᶠ z in nhdsWithin x (Set.Ioi x), slope ρ x z < r) :
    ρ b ≤ ∫ t in a..b, φ t := by
  set B : ℝ → ℝ := fun x => ∫ t in a..x, φ t with hB
  have hφii : IntervalIntegrable φ volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]; exact hφint
  have hBa : ρ a ≤ B a := by simp [hB, hρa]
  have hBcont : ContinuousOn B (Set.Icc a b) := by
    have h := continuousOn_primitive_interval' (f := φ) (μ := volume) (a := a)
      (b₁ := a) (b₂ := b) hφii Set.left_mem_uIcc
    rw [Set.uIcc_of_le hab] at h; exact h
  have hBderiv : ∀ x ∈ Set.Ico a b, HasDerivWithinAt B (φ x) (Set.Ici x) x := by
    intro x hx
    have hcwa : ContinuousWithinAt φ (Set.Ioi x) x := hφcont x hx
    have hmem : Set.Icc a b ∈ nhdsWithin x (Set.Ioi x) := by
      rw [mem_nhdsWithin]
      exact ⟨Set.Iio b, isOpen_Iio, hx.2, by
        intro z hz; exact ⟨le_trans hx.1 (le_of_lt hz.2), le_of_lt hz.1⟩⟩
    have hmeas : StronglyMeasurableAtFilter φ (nhdsWithin x (Set.Ioi x)) volume :=
      ⟨Set.Icc a b, hmem, hφint.aestronglyMeasurable⟩
    have hint_sub : IntervalIntegrable φ volume a x :=
      hφii.mono_set (by
        rw [Set.uIcc_of_le hab, Set.uIcc_of_le hx.1]; exact Set.Icc_subset_Icc le_rfl hx.2.le)
    exact intervalIntegral.integral_hasDerivWithinAt_right hint_sub hmeas hcwa
  exact image_le_of_liminf_slope_right_le_deriv_boundary hρc hBa hBcont hBderiv hslope
    (Set.right_mem_Icc.2 hab)

private lemma ftc_fencing_equality_case
    {ρ φ ρ' : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hρc : ContinuousOn ρ (Set.Icc a b))
    (hρderiv : ∀ x ∈ Set.Ioo a b, HasDerivWithinAt ρ (ρ' x) (Set.Ioi x) x)
    (hρ'int : IntervalIntegrable ρ' MeasureTheory.volume a b)
    (hφint : MeasureTheory.IntegrableOn φ (Set.Ioo a b) MeasureTheory.volume)
    (hρ'φ : ∀ x ∈ Set.Ioo a b, ρ' x ≤ φ x)
    (htight : ρ b - ρ a = ∫ t in a..b, φ t) :
    ρ' =ᵐ[MeasureTheory.volume.restrict (Set.Ioo a b)] φ := by
  have hftc : (∫ t in a..b, ρ' t) = ρ b - ρ a :=
    intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab hρc hρderiv hρ'int
  have heqint : (∫ t in a..b, ρ' t) = ∫ t in a..b, φ t := by rw [hftc, htight]
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab] at heqint
  have hconvρ : (∫ t in Set.Ioc a b, ρ' t) = ∫ t in Set.Ioo a b, ρ' t :=
    MeasureTheory.setIntegral_congr_set MeasureTheory.Ioo_ae_eq_Ioc.symm
  have hconvφ : (∫ t in Set.Ioc a b, φ t) = ∫ t in Set.Ioo a b, φ t :=
    MeasureTheory.setIntegral_congr_set MeasureTheory.Ioo_ae_eq_Ioc.symm
  rw [hconvρ, hconvφ] at heqint
  have hρ'Ioo : MeasureTheory.IntegrableOn ρ' (Set.Ioo a b) MeasureTheory.volume := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hab] at hρ'int; exact hρ'int
  have hae_le : ρ' ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioo a b)] φ :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo hρ'φ
  exact (MeasureTheory.integral_eq_iff_of_ae_le hρ'Ioo hφint hae_le).mp heqint

end RadialLengthAnalyticEngine

end Riemannian
end Geometry
end DifferentialGeometry
