import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricCompactness
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.GoodCovering
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.GoodCoveringItem3
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepBInputs
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.VolumeComparisonBridge

set_option autoImplicit false
set_option linter.style.longLine false























































noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Filter
open scoped Manifold ContDiff Topology

variable {E : Type uE} [NormedAddCommGroup E]
variable [NormedSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable [I.Boundaryless]









structure NormalRadiusProfile
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjRadiusDecayInput (I := I) X)
    (hb : NormalCoordMetricBoundInput (I := I) X) where
  ratio : Real
  ratio_pos : 0 < ratio
  le_radius : ∀ k x,
    ratio * hd.mu (hd.dist k x (X.obj k).basepoint) ≤ hb.radius k x
  le_exp_radius : ∀ k x,
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
    letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    letI : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
    ratio * hd.mu (hd.dist k x (X.obj k).basepoint) ≤
      Geometry.Riemannian.expMapC2Radius (I := I) (X.obj k).metric x

namespace NormalRadiusProfile


def subseq
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    {hb : NormalCoordMetricBoundInput (I := I) X}
    (h : NormalRadiusProfile hd hb) (f : Nat → Nat) :
    NormalRadiusProfile (hd.subseq f) (hb.subseq f) where
  ratio := h.ratio
  ratio_pos := h.ratio_pos
  le_radius := by
    intro k x
    change h.ratio * hd.mu (hd.dist (f k) x (X.obj (f k)).basepoint) ≤
      hb.radius (f k) x
    exact h.le_radius (f k) x
  le_exp_radius := by
    intro k x
    letI : TopologicalSpace (X.obj (f k)).M := (X.obj (f k)).topology
    letI : ChartedSpace H (X.obj (f k)).M := (X.obj (f k)).charted
    letI : IsManifold I ∞ (X.obj (f k)).M := (X.obj (f k)).smooth
    letI : T2Space (TangentBundle I (X.obj (f k)).M) :=
      (X.obj (f k)).t2TangentBundle
    change h.ratio * hd.mu (hd.dist (f k) x (X.obj (f k)).basepoint) ≤
      Geometry.Riemannian.expMapC2Radius (I := I) (X.obj (f k)).metric x
    exact h.le_exp_radius (f k) x



def gpRatio
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    {hb : NormalCoordMetricBoundInput (I := I) X}
    (h : NormalRadiusProfile hd hb) : Real :=
  Real.sqrt (1 / 2 : Real) * h.ratio


theorem gpRatio_pos
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    {hb : NormalCoordMetricBoundInput (I := I) X}
    (h : NormalRadiusProfile hd hb) : 0 < h.gpRatio := by
  rw [gpRatio]
  exact mul_pos (Real.sqrt_pos.mpr (by norm_num)) h.ratio_pos



theorem gpRatio_le_ratio
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    {hb : NormalCoordMetricBoundInput (I := I) X}
    (h : NormalRadiusProfile hd hb) : h.gpRatio ≤ h.ratio := by
  rw [gpRatio]
  have hsqrt : Real.sqrt (1 / 2 : Real) ≤ 1 :=
    Real.sqrt_le_one.mpr (by norm_num)
  simpa only [one_mul] using
    mul_le_mul_of_nonneg_right hsqrt h.ratio_pos.le



theorem floor_pos
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    {hb : NormalCoordMetricBoundInput (I := I) X}
    (h : NormalRadiusProfile hd hb) (R : Real) :
    0 < h.ratio * hd.mu R :=
  mul_pos h.ratio_pos (hd.mu_pos R)



theorem floor_le_radius
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    {hb : NormalCoordMetricBoundInput (I := I) X}
    (h : NormalRadiusProfile hd hb) {k : Nat} {x : (X.obj k).M} {R : Real}
    (hx : hd.dist k x (X.obj k).basepoint ≤ R) :
    h.ratio * hd.mu R ≤ hb.radius k x := by
  calc
    h.ratio * hd.mu R ≤
        h.ratio * hd.mu (hd.dist k x (X.obj k).basepoint) :=
      mul_le_mul_of_nonneg_left (hd.mu_antitone hx) h.ratio_pos.le
    _ ≤ hb.radius k x := h.le_radius k x



theorem floor_le_exp
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    {hb : NormalCoordMetricBoundInput (I := I) X}
    (h : NormalRadiusProfile hd hb) {k : Nat} {x : (X.obj k).M} {R : Real}
    (hx : hd.dist k x (X.obj k).basepoint ≤ R) :
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
    letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    letI : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
    h.ratio * hd.mu R ≤
      Geometry.Riemannian.expMapC2Radius (I := I) (X.obj k).metric x := by
  letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
  letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
  letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  letI : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
  calc
    h.ratio * hd.mu R ≤
        h.ratio * hd.mu (hd.dist k x (X.obj k).basepoint) :=
      mul_le_mul_of_nonneg_left (hd.mu_antitone hx) h.ratio_pos.le
    _ ≤ Geometry.Riemannian.expMapC2Radius (I := I) (X.obj k).metric x :=
      h.le_exp_radius k x



theorem floor_le_expGp
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    {hb : NormalCoordMetricBoundInput (I := I) X}
    (h : NormalRadiusProfile hd hb) {k : Nat} {x : (X.obj k).M} {R : Real}
    (hx : hd.dist k x (X.obj k).basepoint ≤ R) :
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
    letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    letI : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
    h.gpRatio * hd.mu R ≤
      Geometry.Riemannian.expRadiusGp (I := I) (X.obj k).metric x := by
  letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
  letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
  letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  letI : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
  rw [gpRatio, Geometry.Riemannian.expRadiusGp]
  calc
    Real.sqrt (1 / 2 : Real) * h.ratio * hd.mu R =
        Real.sqrt (1 / 2 : Real) * (h.ratio * hd.mu R) := by ring
    _ ≤ Real.sqrt (Geometry.Riemannian.gpCoerciveConst
          (I := I) (X.obj k).metric x) * (h.ratio * hd.mu R) :=
      mul_le_mul_of_nonneg_right
        (Real.sqrt_le_sqrt (hb.half_le_gpConst k x)) (h.floor_pos R).le
    _ ≤ Real.sqrt (Geometry.Riemannian.gpCoerciveConst
          (I := I) (X.obj k).metric x) *
          Geometry.Riemannian.expMapC2Radius (I := I) (X.obj k).metric x :=
      mul_le_mul_of_nonneg_left (h.floor_le_exp hx) (Real.sqrt_nonneg _)



theorem mul_lambda_lt_floor
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    {hb : NormalCoordMetricBoundInput (I := I) X}
    (h : NormalRadiusProfile hd hb) {D c R : Real}
    (hD : 0 < D) (hc : c < h.ratio * D) :
    c * hd.lambda D R < h.ratio * hd.mu R := by
  rw [InjRadiusDecayInput.lambda]
  calc
    c * (hd.mu R / D) = (c / D) * hd.mu R := by ring
    _ < h.ratio * hd.mu R :=
      mul_lt_mul_of_pos_right ((div_lt_iff₀ hD).2 hc) (hd.mu_pos R)



theorem mul_lambda_lt_radius
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    {hb : NormalCoordMetricBoundInput (I := I) X}
    (h : NormalRadiusProfile hd hb) {D c R : Real}
    (hD : 0 < D) (hc : c < h.ratio * D)
    {k : Nat} {x : (X.obj k).M}
    (hx : hd.dist k x (X.obj k).basepoint ≤ R) :
    c * hd.lambda D R < hb.radius k x :=
  (h.mul_lambda_lt_floor hD hc).trans_le (h.floor_le_radius hx)



theorem mul_lambda_lt_exp
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    {hb : NormalCoordMetricBoundInput (I := I) X}
    (h : NormalRadiusProfile hd hb) {D c R : Real}
    (hD : 0 < D) (hc : c < h.ratio * D)
    {k : Nat} {x : (X.obj k).M}
    (hx : hd.dist k x (X.obj k).basepoint ≤ R) :
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
    letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    letI : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
    c * hd.lambda D R <
      Geometry.Riemannian.expMapC2Radius (I := I) (X.obj k).metric x := by
  letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
  letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
  letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  letI : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
  exact (h.mul_lambda_lt_floor hD hc).trans_le (h.floor_le_exp hx)



theorem mul_lambda_lt_expGp
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    {hb : NormalCoordMetricBoundInput (I := I) X}
    (h : NormalRadiusProfile hd hb) {D c R : Real}
    (hD : 0 < D) (hc : c < h.gpRatio * D)
    {k : Nat} {x : (X.obj k).M}
    (hx : hd.dist k x (X.obj k).basepoint ≤ R) :
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
    letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    letI : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
    c * hd.lambda D R <
      Geometry.Riemannian.expRadiusGp (I := I) (X.obj k).metric x := by
  letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
  letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
  letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  letI : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
  have hfloor : c * hd.lambda D R < h.gpRatio * hd.mu R := by
    rw [InjRadiusDecayInput.lambda]
    calc
      c * (hd.mu R / D) = (c / D) * hd.mu R := by ring
      _ < h.gpRatio * hd.mu R :=
        mul_lt_mul_of_pos_right ((div_lt_iff₀ hD).2 hc) (hd.mu_pos R)
  exact hfloor.trans_le (h.floor_le_expGp hx)




theorem gpScaleTail
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    {hb : NormalCoordMetricBoundInput (I := I) X}
    (h : NormalRadiusProfile hd hb) {D : Real} (hD : 0 < D)
    (h8 : (8 : Real) < h.gpRatio * D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (hre : hd.RealizesEdist) (L : NetLimitData (I := I) hd D P)
    (pb : hd.PackingBound D) (r : Real) :
    Item3GpScaleTail (I := I) hd D P L pb r := by
  have hwin : ∀ᶠ n in atTop, ∀ γ ∈ Finset.range (pb.A r),
      L.lamInf γ / 2 ≤ hd.lambda D (seqRadius hd D P (L.φ n) γ) :=
    (Filter.eventually_all_finset _).mpr fun γ _ =>
      (L.lambda_window hd hD P γ).mono fun _ hγ => by
        simpa only [NetLimitData.lamInf] using hγ.1
  filter_upwards [hwin] with n hn
  intro γ c hc
  letI : MetricSpace (X.obj (L.φ n)).M := (P (L.φ n)).ms
  haveI : ProperSpace (X.obj (L.φ n)).M := (P (L.φ n)).proper
  have hr : seqRadius hd D P (L.φ n) (γ : Nat) =
      dist c (X.obj (L.φ n)).basepoint := by
    unfold seqRadius
    exact OrderedNet.netRadius_of_center _ _ _ (γ : Nat) hc
  have hx : hd.dist (L.φ n) c (X.obj (L.φ n)).basepoint ≤
      seqRadius hd D P (L.φ n) (γ : Nat) := by
    rw [← ProperMetricOn.dist_eq hd hre P (L.φ n), ← hr]
  letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
  letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
  letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
  letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
  letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
    (X.obj (L.φ n)).t2TangentBundle
  calc
    4 * L.lamInf (γ : Nat) = 8 * (L.lamInf (γ : Nat) / 2) := by ring
    _ ≤ 8 * hd.lambda D (seqRadius hd D P (L.φ n) (γ : Nat)) :=
      mul_le_mul_of_nonneg_left
        (hn (γ : Nat) (Finset.mem_range.mpr γ.isLt)) (by norm_num)
    _ < Geometry.Riemannian.expRadiusGp
          (I := I) (X.obj (L.φ n)).metric c :=
      h.mul_lambda_lt_expGp (D := D) (c := 8)
        (R := seqRadius hd D P (L.φ n) (γ : Nat)) hD h8 hx





theorem halfGpScaleTail
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    {hb : NormalCoordMetricBoundInput (I := I) X}
    (h : NormalRadiusProfile hd hb) {D a : Real} (hD : 0 < D)
    (ha : 0 < a) (haRatio : 2 * a < h.ratio * D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (hre : hd.RealizesEdist) (L : NetLimitData (I := I) hd D P)
    (pb : hd.PackingBound D) (r : Real) :
    ∀ᶠ n in atTop, ∀ γ : Fin (pb.A r), ∀ c : (X.obj (L.φ n)).M,
      seqCenter hd D P (L.φ n) (γ : Nat) = some c →
        letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
        letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
        letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
        letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
        letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
          (X.obj (L.φ n)).t2TangentBundle
        (a / 2) * L.lamInf (γ : Nat) <
          Geometry.Riemannian.expRadiusGp
            (I := I) (X.obj (L.φ n)).metric c := by
  have hsqrt : (1 / 2 : Real) < Real.sqrt (1 / 2 : Real) := by
    have hsqrtSq := Real.sq_sqrt (by norm_num : (0 : Real) ≤ 1 / 2)
    have hsqrtNonneg := Real.sqrt_nonneg (1 / 2 : Real)
    nlinarith
  have hratioD : 0 < h.ratio * D := mul_pos h.ratio_pos hD
  have haGp : a < h.gpRatio * D := by
    calc
      a < (1 / 2 : Real) * (h.ratio * D) := by nlinarith
      _ < Real.sqrt (1 / 2 : Real) * (h.ratio * D) :=
        mul_lt_mul_of_pos_right hsqrt hratioD
      _ = h.gpRatio * D := by rw [gpRatio]; ring
  have hwin : ∀ᶠ n in atTop, ∀ γ ∈ Finset.range (pb.A r),
      L.lamInf γ / 2 ≤ hd.lambda D (seqRadius hd D P (L.φ n) γ) :=
    (Filter.eventually_all_finset _).mpr fun γ _ =>
      (L.lambda_window hd hD P γ).mono fun _ hγ => by
        simpa only [NetLimitData.lamInf] using hγ.1
  filter_upwards [hwin] with n hn
  intro γ c hc
  letI : MetricSpace (X.obj (L.φ n)).M := (P (L.φ n)).ms
  haveI : ProperSpace (X.obj (L.φ n)).M := (P (L.φ n)).proper
  have hr : seqRadius hd D P (L.φ n) (γ : Nat) =
      dist c (X.obj (L.φ n)).basepoint := by
    unfold seqRadius
    exact OrderedNet.netRadius_of_center _ _ _ (γ : Nat) hc
  have hx : hd.dist (L.φ n) c (X.obj (L.φ n)).basepoint ≤
      seqRadius hd D P (L.φ n) (γ : Nat) := by
    rw [← ProperMetricOn.dist_eq hd hre P (L.φ n), ← hr]
  letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
  letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
  letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
  letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
  letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
    (X.obj (L.φ n)).t2TangentBundle
  calc
    (a / 2) * L.lamInf (γ : Nat) =
        a * (L.lamInf (γ : Nat) / 2) := by ring
    _ ≤ a * hd.lambda D (seqRadius hd D P (L.φ n) (γ : Nat)) :=
      mul_le_mul_of_nonneg_left
        (hn (γ : Nat) (Finset.mem_range.mpr γ.isLt)) ha.le
    _ < Geometry.Riemannian.expRadiusGp
          (I := I) (X.obj (L.φ n)).metric c :=
      h.mul_lambda_lt_expGp (D := D) (c := a)
        (R := seqRadius hd D P (L.φ n) (γ : Nat)) hD haGp hx



theorem metricScaleTail
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    {hb : NormalCoordMetricBoundInput (I := I) X}
    (h : NormalRadiusProfile hd hb) {D a : Real} (hD : 0 < D)
    (ha : 0 < a) (haRatio : 2 * a < h.ratio * D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (hre : hd.RealizesEdist) (L : NetLimitData (I := I) hd D P)
    (pb : hd.PackingBound D) (r : Real) :
    ∀ᶠ n in atTop, ∀ γ : Fin (pb.A r), ∀ c : (X.obj (L.φ n)).M,
      seqCenter hd D P (L.φ n) (γ : Nat) = some c →
        a * L.lamInf (γ : Nat) ≤ hb.radius (L.φ n) c := by
  have hwin : ∀ᶠ n in atTop, ∀ γ ∈ Finset.range (pb.A r),
      L.lamInf γ / 2 ≤ hd.lambda D (seqRadius hd D P (L.φ n) γ) :=
    (Filter.eventually_all_finset _).mpr fun γ _ =>
      (L.lambda_window hd hD P γ).mono fun _ hγ => by
        simpa only [NetLimitData.lamInf] using hγ.1
  filter_upwards [hwin] with n hn
  intro γ c hc
  letI : MetricSpace (X.obj (L.φ n)).M := (P (L.φ n)).ms
  haveI : ProperSpace (X.obj (L.φ n)).M := (P (L.φ n)).proper
  have hr : seqRadius hd D P (L.φ n) (γ : Nat) =
      dist c (X.obj (L.φ n)).basepoint := by
    unfold seqRadius
    exact OrderedNet.netRadius_of_center _ _ _ (γ : Nat) hc
  have hx : hd.dist (L.φ n) c (X.obj (L.φ n)).basepoint ≤
      seqRadius hd D P (L.φ n) (γ : Nat) := by
    rw [← ProperMetricOn.dist_eq hd hre P (L.φ n), ← hr]
  calc
    a * L.lamInf (γ : Nat) =
        (2 * a) * (L.lamInf (γ : Nat) / 2) := by ring
    _ ≤ (2 * a) * hd.lambda D
        (seqRadius hd D P (L.φ n) (γ : Nat)) :=
      mul_le_mul_of_nonneg_left
        (hn (γ : Nat) (Finset.mem_range.mpr γ.isLt)) (by positivity)
    _ ≤ h.ratio * hd.mu
        (seqRadius hd D P (L.φ n) (γ : Nat)) :=
      (h.mul_lambda_lt_floor hD haRatio).le
    _ ≤ h.ratio * hd.mu
        (hd.dist (L.φ n) c (X.obj (L.φ n)).basepoint) :=
      mul_le_mul_of_nonneg_left (hd.mu_antitone hx) h.ratio_pos.le
    _ ≤ hb.radius (L.φ n) c := h.le_radius (L.φ n) c




theorem radiusScaleTail
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    {hb : NormalCoordMetricBoundInput (I := I) X}
    (h : NormalRadiusProfile hd hb) {D a : Real} (hD : 0 < D) (ha : 0 < a)
    (haD : 2 * a < D) (haRatio : 2 * a < h.ratio * D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (hre : hd.RealizesEdist) (L : NetLimitData (I := I) hd D P)
    (pb : hd.PackingBound D) (r : Real) :
    Item3RadiusTail (I := I) hd D P L pb r a := by
  have hwin : ∀ᶠ n in atTop, ∀ γ ∈ Finset.range (pb.A r),
      L.lamInf γ / 2 ≤ hd.lambda D (seqRadius hd D P (L.φ n) γ) :=
    (Filter.eventually_all_finset _).mpr fun γ _ =>
      (L.lambda_window hd hD P γ).mono fun _ hγ => by
        simpa only [NetLimitData.lamInf] using hγ.1
  filter_upwards [hwin] with n hn
  intro γ c hc
  letI : MetricSpace (X.obj (L.φ n)).M := (P (L.φ n)).ms
  haveI : ProperSpace (X.obj (L.φ n)).M := (P (L.φ n)).proper
  have hr : seqRadius hd D P (L.φ n) (γ : Nat) =
      dist c (X.obj (L.φ n)).basepoint := by
    unfold seqRadius
    exact OrderedNet.netRadius_of_center _ _ _ (γ : Nat) hc
  have hx : hd.dist (L.φ n) c (X.obj (L.φ n)).basepoint ≤
      seqRadius hd D P (L.φ n) (γ : Nat) := by
    rw [← ProperMetricOn.dist_eq hd hre P (L.φ n), ← hr]
  letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
  letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
  letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
  letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
  letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
  letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
    (X.obj (L.φ n)).t2TangentBundle
  have hrad_pos : 0 < a * L.lamInf (γ : Nat) :=
    mul_pos ha (hd.lambda_pos hD (L.rInf (γ : Nat)))
  have hrad_mu : a * L.lamInf (γ : Nat) <
      hd.mu (seqRadius hd D P (L.φ n) (γ : Nat)) := by
    calc
      a * L.lamInf (γ : Nat) =
          (2 * a) * (L.lamInf (γ : Nat) / 2) := by ring
      _ ≤ (2 * a) * hd.lambda D
          (seqRadius hd D P (L.φ n) (γ : Nat)) :=
        mul_le_mul_of_nonneg_left
          (hn (γ : Nat) (Finset.mem_range.mpr γ.isLt)) (by positivity)
      _ < D * hd.lambda D (seqRadius hd D P (L.φ n) (γ : Nat)) :=
        mul_lt_mul_of_pos_right haD
          (hd.lambda_pos hD (seqRadius hd D P (L.φ n) (γ : Nat)))
      _ = hd.mu (seqRadius hd D P (L.φ n) (γ : Nat)) := by
        rw [InjRadiusDecayInput.lambda]
        exact mul_div_cancel₀ _ hD.ne'
  have hmu := hd.mu_hasInj_of_le hx
  rw [hasInjRadiusAt_iff] at hmu
  have hinj : ENNReal.ofReal (a * L.lamInf (γ : Nat)) <
      Geometry.Riemannian.injRadius (I := I) (X.obj (L.φ n)).metric c :=
    ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg hrad_pos.le).2 hrad_mu).trans_le hmu.2
  have hrad_lambda : a * L.lamInf (γ : Nat) ≤
      (2 * a) * hd.lambda D (seqRadius hd D P (L.φ n) (γ : Nat)) := by
    calc
      a * L.lamInf (γ : Nat) =
          (2 * a) * (L.lamInf (γ : Nat) / 2) := by ring
      _ ≤ (2 * a) * hd.lambda D
          (seqRadius hd D P (L.φ n) (γ : Nat)) :=
        mul_le_mul_of_nonneg_left
          (hn (γ : Nat) (Finset.mem_range.mpr γ.isLt)) (by positivity)
  have hexp := h.mul_lambda_lt_exp (D := D) (c := 2 * a)
    (R := seqRadius hd D P (L.φ n) (γ : Nat)) hD haRatio hx
  exact ⟨hinj, hrad_lambda.trans hexp.le⟩

end NormalRadiusProfile







structure MetricCompactBase
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I)) where

  decay : InjRadiusDecayInput (I := I) X

  pack : ∀ D : Real, 0 < D → decay.PackingBound D

  volume : VolumeComparisonInput (I := I) X

  dist_eq : volume.dist = decay.dist

  realizes : decay.RealizesEdist

  normalBounds : NormalCoordMetricBoundInput (I := I) X

  normalRadius : NormalRadiusProfile decay normalBounds

namespace MetricCompactBase




theorem exists_largeD
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (b : MetricCompactBase (I := I) X) (c : Real) :
    ∃ D : Real, 1 < D ∧
      b.decay.mu 0 ≤ D ∧
      c < b.normalRadius.gpRatio * D ∧
      max 4 (50 * Real.exp (b.decay.C * (20 * b.decay.lambda D 0))) *
        b.decay.lambda D 0 ≤ b.volume.r0 := by
  let q : Real :=
    b.decay.a * (min b.decay.baseInj.ρ 1) ^ (Module.finrank Real E)
  let K : Real := max 4 (50 * Real.exp (b.decay.C * 20))
  let B : Real := max 1
    (max q (max (K * q / b.volume.r0) (c / b.normalRadius.gpRatio)))
  let D : Real := B + 1
  have hB_lt : B < D := by
    dsimp only [D]
    linarith
  have honeB : (1 : Real) ≤ B := by
    dsimp only [B]
    exact le_max_left _ _
  have hqB : q ≤ B := by
    dsimp only [B]
    exact (le_max_left q _).trans (le_max_right 1 _)
  have hcapB : K * q / b.volume.r0 ≤ B := by
    dsimp only [B]
    exact ((le_max_left (K * q / b.volume.r0) _).trans
      (le_max_right q _)).trans (le_max_right 1 _)
  have hcB : c / b.normalRadius.gpRatio ≤ B := by
    dsimp only [B]
    exact ((le_max_right (K * q / b.volume.r0) _).trans
      (le_max_right q _)).trans (le_max_right 1 _)
  have hD_one : (1 : Real) < D := honeB.trans_lt hB_lt
  have hD : 0 < D := zero_lt_one.trans hD_one
  have hqD : q ≤ D := hqB.trans hB_lt.le
  have hmuD : b.decay.mu 0 ≤ D := by
    simpa only [InjRadiusDecayInput.mu, q, mul_zero, Real.exp_zero, mul_one]
      using hqD
  have hlam_le : b.decay.lambda D 0 ≤ 1 :=
    b.decay.lambda_le_one_at_zero (by simpa only [q] using hqD)
  have hlam_nonneg : 0 ≤ b.decay.lambda D 0 :=
    (b.decay.lambda_pos hD 0).le
  have harg :
      b.decay.C * (20 * b.decay.lambda D 0) ≤ b.decay.C * 20 := by
    have h20 : 20 * b.decay.lambda D 0 ≤ (20 : Real) := by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hlam_le (by norm_num : (0 : Real) ≤ 20)
    exact mul_le_mul_of_nonneg_left h20 b.decay.C_nonneg
  have hfac :
      max 4 (50 * Real.exp (b.decay.C * (20 * b.decay.lambda D 0))) ≤ K := by
    dsimp only [K]
    exact max_le_max le_rfl (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr harg) (by norm_num))
  have hKq : K * q < D * b.volume.r0 :=
    (div_lt_iff₀ b.volume.r0_pos).1 (hcapB.trans_lt hB_lt)
  have hKlam : K * b.decay.lambda D 0 < b.volume.r0 := by
    calc
      K * b.decay.lambda D 0 = K * q / D := by
        dsimp only [InjRadiusDecayInput.lambda, InjRadiusDecayInput.mu, q]
        simp only [mul_zero, Real.exp_zero, mul_one]
        ring
      _ < b.volume.r0 := (div_lt_iff₀ hD).2 (by
        simpa only [mul_comm] using hKq)
  have hc : c < b.normalRadius.gpRatio * D := by
    simpa only [mul_comm] using
      (div_lt_iff₀ b.normalRadius.gpRatio_pos).1 (hcB.trans_lt hB_lt)
  refine ⟨D, hD_one, hmuD, hc, ?_⟩
  exact (mul_le_mul_of_nonneg_right hfac hlam_nonneg).trans hKlam.le




theorem exists_item3D
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (b : MetricCompactBase (I := I) X) (c₀ : Real) :
    ∃ D : Real, 1 < D ∧
      b.decay.mu 0 ≤ D ∧
      c₀ < b.normalRadius.gpRatio * D ∧
      (8 : Real) < b.normalRadius.gpRatio * D ∧
      (16 : Real) < b.normalRadius.ratio * D ∧
      2 * item3RadiusFactor b.decay D < D ∧
      2 * item3RadiusFactor b.decay D < b.normalRadius.ratio * D ∧
      max 4 (50 * Real.exp (b.decay.C * (20 * b.decay.lambda D 0))) *
        b.decay.lambda D 0 ≤ b.volume.r0 := by
  let Q : Real := 410 * Real.exp (b.decay.C * 20)
  let c : Real := max c₀ (max 8
    (max Q (Q * b.normalRadius.gpRatio)))
  obtain ⟨D, hD_one, hmuD, hc, hcap⟩ := b.exists_largeD c
  have hD : 0 < D := zero_lt_one.trans hD_one
  have hc₀c : c₀ ≤ c := by
    dsimp only [c]
    exact le_max_left _ _
  have h8c : (8 : Real) ≤ c := by
    dsimp only [c]
    exact (le_max_left (8 : Real) _).trans (le_max_right c₀ _)
  have hQc : Q ≤ c := by
    dsimp only [c]
    exact ((le_max_left Q _).trans (le_max_right 8 _)).trans
      (le_max_right c₀ _)
  have hQgc : Q * b.normalRadius.gpRatio ≤ c := by
    dsimp only [c]
    exact ((le_max_right Q _).trans (le_max_right 8 _)).trans
      (le_max_right c₀ _)
  have hc₀ : c₀ < b.normalRadius.gpRatio * D := hc₀c.trans_lt hc
  have h8 : (8 : Real) < b.normalRadius.gpRatio * D := h8c.trans_lt hc
  have hQgp : Q < b.normalRadius.gpRatio * D := hQc.trans_lt hc
  have hQg : Q * b.normalRadius.gpRatio <
      b.normalRadius.gpRatio * D := hQgc.trans_lt hc
  have hQD : Q < D := by
    exact lt_of_mul_lt_mul_right (by simpa only [mul_comm] using hQg)
      b.normalRadius.gpRatio_pos.le
  have hQratio : Q < b.normalRadius.ratio * D := by
    exact hQgp.trans_le (mul_le_mul_of_nonneg_right
      b.normalRadius.gpRatio_le_ratio hD.le)
  have h16Q : (16 : Real) ≤ Q := by
    dsimp only [Q]
    have hexp : (1 : Real) ≤ Real.exp (b.decay.C * 20) :=
      Real.one_le_exp (mul_nonneg b.decay.C_nonneg (by norm_num))
    calc
      (16 : Real) ≤ 410 * 1 := by norm_num
      _ ≤ 410 * Real.exp (b.decay.C * 20) :=
        mul_le_mul_of_nonneg_left hexp (by norm_num)
  have h16 : (16 : Real) < b.normalRadius.ratio * D :=
    h16Q.trans_lt hQratio
  have hqD :
      b.decay.a * (min b.decay.baseInj.ρ 1) ^ (Module.finrank Real E) ≤ D := by
    simpa only [InjRadiusDecayInput.mu, mul_zero, Real.exp_zero, mul_one]
      using hmuD
  have hlam_le : b.decay.lambda D 0 ≤ 1 :=
    b.decay.lambda_le_one_at_zero hqD
  have harg :
      b.decay.C * (20 * b.decay.lambda D 0) ≤ b.decay.C * 20 := by
    have h20 : 20 * b.decay.lambda D 0 ≤ (20 : Real) := by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hlam_le (by norm_num : (0 : Real) ≤ 20)
    exact mul_le_mul_of_nonneg_left h20 b.decay.C_nonneg
  have hfac : 2 * item3RadiusFactor b.decay D ≤ Q := by
    dsimp only [item3RadiusFactor, Q]
    calc
      2 * (205 * Real.exp (b.decay.C * (20 * b.decay.lambda D 0))) =
          410 * Real.exp (b.decay.C * (20 * b.decay.lambda D 0)) := by ring
      _ ≤ 410 * Real.exp (b.decay.C * 20) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr harg) (by norm_num)
  exact ⟨D, hD_one, hmuD, hc₀, h8, h16, hfac.trans_lt hQD,
    hfac.trans_lt hQratio, hcap⟩

end MetricCompactBase








structure MetricCompactnessInputs
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I)) where

  decay : InjRadiusDecayInput (I := I) X


  D : Real
  hD : 0 < D

  pack : decay.PackingBound D

  volume : VolumeComparisonInput (I := I) X

  dist_eq : volume.dist = decay.dist


  stepA_cap_le :
    max 4 (50 * Real.exp (decay.C * (20 * decay.lambda D 0))) *
      decay.lambda D 0 <= volume.r0

  realizes : decay.RealizesEdist

  normalBounds : NormalCoordMetricBoundInput (I := I) X


  normalRadius : NormalRadiusProfile decay normalBounds

namespace MetricCompactnessInputs



def ofBase
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (b : MetricCompactBase (I := I) X) (D : Real) (hD : 0 < D)
    (hcap :
      max 4 (50 * Real.exp (b.decay.C * (20 * b.decay.lambda D 0))) *
        b.decay.lambda D 0 ≤ b.volume.r0) :
    MetricCompactnessInputs (I := I) X where
  decay := b.decay
  D := D
  hD := hD
  pack := b.pack D hD
  volume := b.volume
  dist_eq := b.dist_eq
  stepA_cap_le := hcap
  realizes := b.realizes
  normalBounds := b.normalBounds
  normalRadius := b.normalRadius



theorem exists_ofBase
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (b : MetricCompactBase (I := I) X) (c : Real) :
    ∃ inp : MetricCompactnessInputs (I := I) X,
      1 < inp.D ∧ inp.decay.mu 0 ≤ inp.D ∧
        c < inp.normalRadius.gpRatio * inp.D := by
  obtain ⟨D, hD_one, hmuD, hc, hcap⟩ := b.exists_largeD c
  have hD : 0 < D := zero_lt_one.trans hD_one
  refine ⟨ofBase b D hD hcap, ?_, ?_, ?_⟩
  · exact hD_one
  · exact hmuD
  · exact hc



theorem exists_item3OfBase
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (b : MetricCompactBase (I := I) X) (c₀ : Real) :
    ∃ inp : MetricCompactnessInputs (I := I) X,
      1 < inp.D ∧ inp.decay.mu 0 ≤ inp.D ∧
      c₀ < inp.normalRadius.gpRatio * inp.D ∧
      (8 : Real) < inp.normalRadius.gpRatio * inp.D ∧
      (16 : Real) < inp.normalRadius.ratio * inp.D ∧
      2 * item3RadiusFactor inp.decay inp.D < inp.D ∧
      2 * item3RadiusFactor inp.decay inp.D <
        inp.normalRadius.ratio * inp.D := by
  obtain ⟨D, hD_one, hmuD, hc₀, h8, h16, hradD, hradRatio, hcap⟩ :=
    b.exists_item3D c₀
  have hD : 0 < D := zero_lt_one.trans hD_one
  refine ⟨ofBase b D hD hcap, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hD_one
  · exact hmuD
  · exact hc₀
  · exact h8
  · exact h16
  · exact hradD
  · exact hradRatio



theorem physScale_of_extra
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (inp : MetricCompactnessInputs (I := I) X) {aMin : Real}
    (haMin : 0 < aMin)
    (hextra :
      (8 * Real.exp inp.decay.C / aMin) * inp.normalRadius.gpRatio <
        inp.normalRadius.gpRatio * inp.D) :
    8 * Real.exp inp.decay.C < aMin * inp.D := by
  have hD : 8 * Real.exp inp.decay.C / aMin < inp.D := by
    exact lt_of_mul_lt_mul_right
      (by simpa only [mul_comm] using hextra) inp.normalRadius.gpRatio_pos.le
  simpa only [mul_comm] using (div_lt_iff₀ haMin).1 hD



theorem item3ScaleTails
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (inp : MetricCompactnessInputs (I := I) X)
    (h8 : (8 : Real) < inp.normalRadius.gpRatio * inp.D)
    (hradD : 2 * item3RadiusFactor inp.decay inp.D < inp.D)
    (hradRatio : 2 * item3RadiusFactor inp.decay inp.D <
      inp.normalRadius.ratio * inp.D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData (I := I) inp.decay inp.D P) (r : Real) :
    Item3GpScaleTail (I := I) inp.decay inp.D P L inp.pack r ∧
      Item3RadiusTail (I := I) inp.decay inp.D P L inp.pack r
        (item3RadiusFactor inp.decay inp.D) := by
  exact ⟨inp.normalRadius.gpScaleTail inp.hD h8 P inp.realizes L inp.pack r,
    inp.normalRadius.radiusScaleTail inp.hD
      (item3Factor_pos inp.decay inp.D) hradD hradRatio
      P inp.realizes L inp.pack r⟩







def ofUniformVolume
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (decay : InjRadiusDecayInput (I := I) X)
    (D : Real) (hD : 0 < D)
    (pack : decay.PackingBound D)
    (vol : UniformBallPack (I := I) X)
    (dist_eq : vol.dist = decay.dist)
    (stepA_cap_le :
      max 4 (50 * Real.exp (decay.C * (20 * decay.lambda D 0))) *
        decay.lambda D 0 ≤ vol.r0)
    (realizes : decay.RealizesEdist)
    (normalBounds : NormalCoordMetricBoundInput (I := I) X)
    (normalRadius : NormalRadiusProfile decay normalBounds) :
    MetricCompactnessInputs (I := I) X where
  decay := decay
  D := D
  hD := hD
  pack := pack
  volume := vol.toVCInput
  dist_eq := by
    change vol.dist = decay.dist
    exact dist_eq
  stepA_cap_le := by
    change max 4 (50 * Real.exp (decay.C * (20 * decay.lambda D 0))) *
      decay.lambda D 0 ≤ vol.r0
    exact stepA_cap_le
  realizes := realizes
  normalBounds := normalBounds
  normalRadius := normalRadius


def subseq
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (inp : MetricCompactnessInputs (I := I) X) (f : Nat -> Nat) :
    MetricCompactnessInputs (I := I) (X.subseq f) where
  decay := inp.decay.subseq f
  D := inp.D
  hD := inp.hD
  pack := inp.pack.subseq f
  volume := inp.volume.subseq f
  dist_eq := by
    funext k x y
    change inp.volume.dist (f k) x y = inp.decay.dist (f k) x y
    rw [inp.dist_eq]
  stepA_cap_le := by
    simpa [InjRadiusDecayInput.subseq, InjRadiusDecayInput.lambda, InjRadiusDecayInput.mu]
      using inp.stepA_cap_le
  realizes := inp.realizes.subseq f
  normalBounds := inp.normalBounds.subseq f
  normalRadius := inp.normalRadius.subseq f




theorem cap_four
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (inp : MetricCompactnessInputs (I := I) X) :
    (4 : Real) * inp.decay.lambda inp.D 0 <= inp.volume.r0 := by
  have hlam : 0 <= inp.decay.lambda inp.D 0 :=
    (inp.decay.lambda_pos inp.hD 0).le
  have hle :
      (4 : Real) <=
        max 4 (50 * Real.exp (inp.decay.C * (20 * inp.decay.lambda inp.D 0))) :=
    le_max_left _ _
  exact (mul_le_mul_of_nonneg_right hle hlam).trans inp.stepA_cap_le





theorem cap_four_of_nonneg
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (inp : MetricCompactnessInputs (I := I) X) {R : Real} (hR : 0 <= R) :
    (4 : Real) * inp.decay.lambda inp.D R <= inp.volume.r0 := by
  have hlam : inp.decay.lambda inp.D R <= inp.decay.lambda inp.D 0 :=
    inp.decay.lambda_antitone inp.hD hR
  have hmul :
      (4 : Real) * inp.decay.lambda inp.D R <=
        (4 : Real) * inp.decay.lambda inp.D 0 :=
    mul_le_mul_of_nonneg_left hlam (by norm_num)
  exact hmul.trans inp.cap_four




theorem cap_inter
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (inp : MetricCompactnessInputs (I := I) X) :
    (50 * Real.exp (inp.decay.C * (20 * inp.decay.lambda inp.D 0))) *
        inp.decay.lambda inp.D 0 <= inp.volume.r0 := by
  have hlam : 0 <= inp.decay.lambda inp.D 0 :=
    (inp.decay.lambda_pos inp.hD 0).le
  have hle :
      50 * Real.exp (inp.decay.C * (20 * inp.decay.lambda inp.D 0)) <=
        max 4 (50 * Real.exp (inp.decay.C * (20 * inp.decay.lambda inp.D 0))) :=
    le_max_right _ _
  exact (mul_le_mul_of_nonneg_right hle hlam).trans inp.stepA_cap_le


theorem net_mult
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (inp : MetricCompactnessInputs (I := I) X) (k : Nat) {R : Real}
    (hR : 0 <= R) {S : Set ((X.obj k).M)}
    (hS : S.PairwiseDisjoint (inp.decay.lambdaBall inp.D k))
    (hSR : ∀ x ∈ S, inp.decay.dist k x (X.obj k).basepoint <= R)
    (z : (X.obj k).M) (J : Finset ((X.obj k).M)) (hJS : ↑J ⊆ S)
    (hJz : ∀ x ∈ J, inp.decay.dist k x z <= 4 * inp.decay.lambda inp.D R) :
    J.card <= inp.volume.Imult 4 := by
  exact InjRadiusDecayInput.net_multiplicity
    inp.decay inp.D k inp.hD inp.realizes inp.volume inp.dist_eq R
    (inp.cap_four_of_nonneg hR) hS hSR z J hJS hJz


theorem inter_count
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) (α : Nat) :
    ∀ᶠ k in atTop,
      ∀ xα : (X.obj (L.φ k)).M,
        seqCenter inp.decay inp.D P (L.φ k) α = some xα →
      ∀ J : Finset Nat,
        (∀ β ∈ J, BInter inp.decay inp.D P L.lamInf α β (L.φ k)) →
        J.card <=
          inp.volume.Imult
            (50 * Real.exp (inp.decay.C * (20 * inp.decay.lambda inp.D 0))) := by
  exact NetLimitData.inter_count inp.decay inp.hD P L inp.realizes inp.pack
    inp.volume inp.dist_eq inp.cap_inter α


theorem exists_net_data
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k)) :
    Nonempty (NetLimitData inp.decay inp.D P) :=
  exists_netLimitData inp.decay inp.hD P


theorem exists_stable_net
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k)) :
    ∃ L : NetLimitData inp.decay inp.D P,
      ∀ α β : Nat,
        (∀ᶠ k in atTop, BInter inp.decay inp.D P L.lamInf α β (L.φ k)) ∨
        (∀ᶠ k in atTop, ¬ BInter inp.decay inp.D P L.lamInf α β (L.φ k)) :=
  exists_stableNetData inp.decay inp.hD P



theorem exists_stepA_net
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k)) :
    ∃ L : NetLimitData inp.decay inp.D P,
      (∀ α β : Nat,
        (∀ᶠ k in atTop, BInter inp.decay inp.D P L.lamInf α β (L.φ k)) ∨
        (∀ᶠ k in atTop, ¬ BInter inp.decay inp.D P L.lamInf α β (L.φ k))) ∧
      (∀ α : Nat,
        ∀ᶠ k in atTop,
          ∀ xα : (X.obj (L.φ k)).M,
            seqCenter inp.decay inp.D P (L.φ k) α = some xα →
          ∀ J : Finset Nat,
            (∀ β ∈ J, BInter inp.decay inp.D P L.lamInf α β (L.φ k)) →
            J.card <=
              inp.volume.Imult
                (50 * Real.exp (inp.decay.C * (20 * inp.decay.lambda inp.D 0)))) := by
  obtain ⟨L, hstable⟩ := inp.exists_stable_net P
  exact ⟨L, hstable, fun α => inp.inter_count P L α⟩



noncomputable def properMetrics
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (_inp : MetricCompactnessInputs (I := I) X)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : forall k : Nat,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M) :
    ∀ k : Nat, ProperMetricOn (I := I) (X.obj k) :=
  fun k => properMetricOn (I := I) (X.obj k) (hcomplete.complete k) (hconn k)


theorem stepA_net
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (inp : MetricCompactnessInputs (I := I) X)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : forall k : Nat,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M) :
    ∃ L : NetLimitData inp.decay inp.D (inp.properMetrics hcomplete hconn),
      (∀ α β : Nat,
        (∀ᶠ k in atTop,
          BInter inp.decay inp.D (inp.properMetrics hcomplete hconn)
            L.lamInf α β (L.φ k)) ∨
        (∀ᶠ k in atTop,
          ¬ BInter inp.decay inp.D (inp.properMetrics hcomplete hconn)
            L.lamInf α β (L.φ k))) ∧
      (∀ α : Nat,
        ∀ᶠ k in atTop,
          ∀ xα : (X.obj (L.φ k)).M,
            seqCenter inp.decay inp.D (inp.properMetrics hcomplete hconn)
              (L.φ k) α = some xα →
          ∀ J : Finset Nat,
            (∀ β ∈ J,
              BInter inp.decay inp.D (inp.properMetrics hcomplete hconn)
                L.lamInf α β (L.φ k)) →
            J.card <=
              inp.volume.Imult
                (50 * Real.exp (inp.decay.C * (20 * inp.decay.lambda inp.D 0)))) :=
  inp.exists_stepA_net (inp.properMetrics hcomplete hconn)



theorem stepA_net_subseq
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (inp : MetricCompactnessInputs (I := I) X)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : forall k : Nat,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (f : Nat -> Nat) :
    ∃ L : NetLimitData (inp.subseq f).decay (inp.subseq f).D
        ((inp.subseq f).properMetrics (hcomplete.subseq f)
          (fun k => by
            simpa [PointedRiemannianSeq.subseq] using hconn (f k))),
      (∀ α β : Nat,
        (∀ᶠ k in atTop,
          BInter (inp.subseq f).decay (inp.subseq f).D
            ((inp.subseq f).properMetrics (hcomplete.subseq f)
              (fun k => by
                simpa [PointedRiemannianSeq.subseq] using hconn (f k)))
            L.lamInf α β (L.φ k)) ∨
        (∀ᶠ k in atTop,
          ¬ BInter (inp.subseq f).decay (inp.subseq f).D
            ((inp.subseq f).properMetrics (hcomplete.subseq f)
              (fun k => by
                simpa [PointedRiemannianSeq.subseq] using hconn (f k)))
            L.lamInf α β (L.φ k))) ∧
      (∀ α : Nat,
        ∀ᶠ k in atTop,
          ∀ xα : ((X.subseq f).obj (L.φ k)).M,
            seqCenter (inp.subseq f).decay (inp.subseq f).D
              ((inp.subseq f).properMetrics (hcomplete.subseq f)
                (fun k => by
                  simpa [PointedRiemannianSeq.subseq] using hconn (f k)))
              (L.φ k) α = some xα →
          ∀ J : Finset Nat,
            (∀ β ∈ J,
              BInter (inp.subseq f).decay (inp.subseq f).D
                ((inp.subseq f).properMetrics (hcomplete.subseq f)
                  (fun k => by
                    simpa [PointedRiemannianSeq.subseq] using hconn (f k)))
                L.lamInf α β (L.φ k)) →
            J.card <=
              (inp.subseq f).volume.Imult
                (50 * Real.exp
                  ((inp.subseq f).decay.C *
                    (20 * (inp.subseq f).decay.lambda (inp.subseq f).D 0)))) := by
  exact (inp.subseq f).stepA_net (hcomplete.subseq f)
    (fun k => by
      simpa [PointedRiemannianSeq.subseq] using hconn (f k))












def metricCompactness
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (_inp : MetricCompactnessInputs (I := I) X)
    (_hcomplete : SeqMetricComplete (I := I) X)
    (_hgeom : SeqBoundedGeometry (I := I) X)
    (_hinj : BaseInjBound (I := I) X)
    (_hconn : forall k : Nat,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M) :
    MetricCompactnessConclusion (I := I) X := by
  sorry

end MetricCompactnessInputs

end HCGCompactness
end DifferentialGeometry
