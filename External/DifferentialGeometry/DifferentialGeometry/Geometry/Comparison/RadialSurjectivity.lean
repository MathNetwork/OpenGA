import DifferentialGeometry.Geometry.Exponential.GaussLemma
import DifferentialGeometry.Geometry.Comparison.HopfRinow
import DifferentialGeometry.Geometry.Exponential.Defs
import DifferentialGeometry.Geometry.Exponential.LocalDiffeomorphism
import DifferentialGeometry.Geometry.Comparison.NormalCoordinates
import DifferentialGeometry.Geometry.Comparison.RiemannianDistContinuity
import DifferentialGeometry.Analysis.Integration.Measure.ChartDensity
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.Riemannian.PathELength
import Mathlib.Analysis.Convex.Star
import Mathlib.Analysis.Convex.PathConnected



attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

noncomputable section

open Set Function Filter Bundle Manifold
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace RadialSurjectivity

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Riemannian.Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable (g : SmoothRiemannianMetric I M)
variable [Bundle.RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]

def gBall (g : SmoothRiemannianMetric I M) (p : M) (R : ℝ) :
    Set (TangentSpace I p) :=
  {v : TangentSpace I p | Real.sqrt (g.inner p v v) ≤ R}

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma gInner_smul_self (g : SmoothRiemannianMetric I M) (p : M)
    (b : ℝ) (v : TangentSpace I p) :
    g.inner p (b • v) (b • v) = b ^ 2 * g.inner p v v := by
  rw [(g.inner p).map_smul b v, ContinuousLinearMap.smul_apply,
    (g.inner p v).map_smul b v]
  simp only [smul_eq_mul]
  ring

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma sqrt_gInner_smul_self (g : SmoothRiemannianMetric I M) (p : M)
    {b : ℝ} (hb : 0 ≤ b) (v : TangentSpace I p) :
    Real.sqrt (g.inner p (b • v) (b • v)) =
      b * Real.sqrt (g.inner p v v) := by
  rw [gInner_smul_self (I := I) g p b v, Real.sqrt_mul (sq_nonneg b),
    Real.sqrt_sq hb]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma zero_mem_gBall (g : SmoothRiemannianMetric I M) (p : M) {R : ℝ}
    (hR : 0 ≤ R) : (0 : TangentSpace I p) ∈ gBall (I := I) g p R := by
  have h0 : g.inner p (0 : TangentSpace I p) (0 : TangentSpace I p) = 0 := by
    simp
  change Real.sqrt (g.inner p (0 : TangentSpace I p) (0 : TangentSpace I p)) ≤ R
  rw [h0, Real.sqrt_zero]
  exact hR

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma starConvex_gBall (g : SmoothRiemannianMetric I M) (p : M) (R : ℝ) :
    StarConvex ℝ (0 : TangentSpace I p) (gBall (I := I) g p R) := by
  intro y hy a b ha hb hab
  have hb_le_one : b ≤ 1 := by linarith
  have hy' : Real.sqrt (g.inner p y y) ≤ R := hy
  have hsqrt_nonneg : 0 ≤ Real.sqrt (g.inner p y y) := Real.sqrt_nonneg _
  change Real.sqrt (g.inner p (a • (0 : TangentSpace I p) + b • y)
      (a • (0 : TangentSpace I p) + b • y)) ≤ R
  rw [smul_zero, zero_add]
  rw [sqrt_gInner_smul_self (I := I) g p hb y]
  calc b * Real.sqrt (g.inner p y y)
      ≤ 1 * Real.sqrt (g.inner p y y) :=
        mul_le_mul_of_nonneg_right hb_le_one hsqrt_nonneg
    _ = Real.sqrt (g.inner p y y) := one_mul _
    _ ≤ R := hy'

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem gBall_isPreconnected (g : SmoothRiemannianMetric I M) (p : M)
    {R : ℝ} (hR : 0 ≤ R) :
    IsPreconnected (gBall (I := I) g p R) :=
  ((starConvex_gBall (I := I) g p R).isPathConnected
    (zero_mem_gBall (I := I) g p hR)).isConnected.isPreconnected

def radialMinSet (g : SmoothRiemannianMetric I M) (p : M) : Set M :=
  {q : M | ∃ v : TangentSpace I p,
    expMap (I := I) g p v = q ∧
      ENNReal.ofReal (Real.sqrt (g.inner p v v)) = riemannianEDist I p q}

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem p_mem_radialMinSet [T2Space (TangentBundle I M)]
    (g : SmoothRiemannianMetric I M) (p : M) :
    p ∈ radialMinSet (I := I) g p := by
  refine ⟨(0 : TangentSpace I p), expMap_zero (I := I) g p, ?_⟩
  have h0 : g.inner p (0 : TangentSpace I p) (0 : TangentSpace I p) = 0 := by
    simp
  rw [h0, Real.sqrt_zero, ENNReal.ofReal_zero, riemannianEDist_self]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma gInner_self_nonneg (g : SmoothRiemannianMetric I M) (p : M)
    (v : TangentSpace I p) : 0 ≤ g.inner p v v := by
  rcases eq_or_ne v 0 with hv | hv
  · subst hv; simp
  · exact (g.pos p v hv).le

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma continuous_gInner_self (g : SmoothRiemannianMetric I M) (p : M) :
    Continuous (fun v : TangentSpace I p => g.inner p v v) :=
  (g.inner p).continuous.clm_apply continuous_id

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma continuous_sqrt_gInner_self (g : SmoothRiemannianMetric I M)
    (p : M) :
    Continuous (fun v : TangentSpace I p => Real.sqrt (g.inner p v v)) :=
  Real.continuous_sqrt.comp (continuous_gInner_self (I := I) g p)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma isClosed_gBall (g : SmoothRiemannianMetric I M) (p : M)
    (R : ℝ) : IsClosed (gBall (I := I) g p R) := by
  have hpre : gBall (I := I) g p R =
      (fun v : TangentSpace I p => Real.sqrt (g.inner p v v)) ⁻¹' Set.Iic R := by
    ext v; simp only [gBall, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Iic]
  rw [hpre]
  exact IsClosed.preimage (continuous_sqrt_gInner_self (I := I) g p) isClosed_Iic

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma isBounded_gBall (g : SmoothRiemannianMetric I M) (p : M)
    (R : ℝ) : Bornology.IsBounded (gBall (I := I) g p R) := by
  rcases lt_or_ge R 0 with hR | hR
  · have hempty : gBall (I := I) g p R = ∅ := by
      ext v
      simp only [gBall, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]
      exact lt_of_lt_of_le hR (Real.sqrt_nonneg _)
    rw [hempty]; exact Bornology.isBounded_empty
  · obtain ⟨r, hr⟩ :=
      (NormedSpace.isVonNBounded_iff' ℝ (E := TangentSpace I p)).1 (g.isVonNBounded p)
    rw [isBounded_iff_forall_norm_le]
    refine ⟨(R + 1) * r, fun v hv => ?_⟩
    have hsqrt : Real.sqrt (g.inner p v v) ≤ R := hv
    have hnonneg : 0 ≤ g.inner p v v := gInner_self_nonneg (I := I) g p v
    have hgvv : g.inner p v v ≤ R ^ 2 := by
      nlinarith [Real.sq_sqrt hnonneg, Real.sqrt_nonneg (g.inner p v v), hsqrt]
    have hRpos : (0 : ℝ) < R + 1 := by linarith
    set w : TangentSpace I p := (R + 1)⁻¹ • v with hw
    have hgw : g.inner p w w < 1 := by
      have hsmul : g.inner p w w = (R + 1)⁻¹ ^ 2 * g.inner p v v :=
        gInner_smul_self (I := I) g p _ v
      rw [hsmul]
      have hinv_sq_pos : (0 : ℝ) < (R + 1)⁻¹ ^ 2 :=
        pow_pos (inv_pos.mpr hRpos) 2
      have hge : 0 ≤ R / (R + 1) := div_nonneg hR hRpos.le
      have hlt : R / (R + 1) < 1 := by rw [div_lt_one hRpos]; linarith
      calc (R + 1)⁻¹ ^ 2 * g.inner p v v
          ≤ (R + 1)⁻¹ ^ 2 * R ^ 2 :=
            mul_le_mul_of_nonneg_left hgvv hinv_sq_pos.le
        _ = (R / (R + 1)) ^ 2 := by
            rw [div_pow]; field_simp
        _ < 1 := by nlinarith [hlt, hge]
    have hwnorm : ‖w‖ ≤ r := hr w hgw
    have hv_eq : v = (R + 1) • w := by
      rw [hw, smul_smul, mul_inv_cancel₀ (ne_of_gt hRpos), one_smul]
    rw [hv_eq, norm_smul, Real.norm_eq_abs, abs_of_pos hRpos]
    exact mul_le_mul_of_nonneg_left hwnorm hRpos.le

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma isCompact_gBall (g : SmoothRiemannianMetric I M) (p : M)
    (R : ℝ) : IsCompact (gBall (I := I) g p R) := by
  haveI : ProperSpace (TangentSpace I p) := FiniteDimensional.proper_real (TangentSpace I p)
  exact Metric.isCompact_of_isClosed_isBounded
    (isClosed_gBall (I := I) g p R) (isBounded_gBall (I := I) g p R)

variable [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
variable [PseudoEMetricSpace M] [T2Space (TangentBundle I M)]
variable [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
variable [IsRiemannianManifold I M] [CompleteSpace M]

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [ConnectedSpace M] [PseudoEMetricSpace M] [T2Space (TangentBundle I M)] [IsRiemannianManifold I M] [CompleteSpace M] in
private lemma continuous_riemannianEDist_ambient
    (p : M) : Continuous (fun q : M => riemannianEDist I p q) := by
  haveI : LocallyCompactSpace M :=
    Manifold.locallyCompact_of_finiteDimensional (M := M) I
  haveI : RegularSpace M := inferInstance
  letI : PseudoEMetricSpace M := PseudoEMetricSpace.ofRiemannianMetric I M
  exact (continuous_const.edist continuous_id)

end RadialSurjectivity
end Riemannian
end Geometry
end DifferentialGeometry

end
