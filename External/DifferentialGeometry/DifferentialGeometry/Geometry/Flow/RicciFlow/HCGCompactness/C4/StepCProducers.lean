import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepCAveragePOU
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.GoodCoveringItem3
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepCTransitionRefine
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.MetricCompactnessInputs
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepCAtomConv
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepCAtomDiagonal
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepCPairTail
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepCSourceCover

set_option autoImplicit false
set_option linter.style.longLine false


















noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Filter Set Bundle Manifold
open scoped Topology Manifold ContDiff ENNReal
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Geometry.Riemannian.Exponential

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

variable {E : Type uE} [NormedAddCommGroup E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}












theorem properBallImgOfRad
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (P : ProperMetricOn (I := I) Y) {c : Y.M} {R : Real}
    (hR :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space Y.M := Y.t2
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      R < expRadiusGp (I := I) Y.metric c) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space Y.M := Y.t2
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    letI : MetricSpace Y.M := P.ms
    (NormalCoordinates.normalChartAt (I := I) Y.metric c) '' Metric.closedBall c R ⊆
      Metric.ball (0 : E) (expMapC2Radius (I := I) Y.metric c) := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space Y.M := Y.t2
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  letI : MetricSpace Y.M := P.ms
  letI : RiemannianBundle (fun x : Y.M => TangentSpace I x) :=
    ⟨Y.metric.toRiemannianMetric⟩
  have hEnorm :
      ∀ x : Y.M, ∀ v : TangentSpace I x,
        ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (Y.metric.inner x v v)) := by
    intro x v
    simpa using
      (DifferentialGeometry.Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := I) Y.metric x v)
  rintro a ⟨q, hq, rfl⟩
  have hdist_le : dist c q ≤ R := by
    simpa [dist_comm] using (Metric.mem_closedBall.mp hq)
  have hed : riemannianEDist I c q = ENNReal.ofReal (dist c q) := by
    have h := P.realizes c q
    simpa [PointedRiemannianManifold.emetricSpace] using h
  have hfin : riemannianEDist I c q ≠ (⊤ : ℝ≥0∞) := by
    rw [hed]; exact ENNReal.ofReal_ne_top
  have hsmall : (riemannianEDist I c q).toReal < expRadiusGp (I := I) Y.metric c := by
    rw [hed, ENNReal.toReal_ofReal (dist_nonneg : 0 ≤ dist c q)]
    exact lt_of_le_of_lt hdist_le hR
  obtain ⟨v, hv_tgt, _hv_dom, hv_len, hy_eq⟩ :=
    metricBall_subset_normalBall (I := I) Y.metric c hEnorm hfin hsmall
  have hchart : NormalCoordinates.normalChartAt (I := I) Y.metric c q = v := by
    have hsymm : (NormalCoordinates.normalChartAt (I := I) Y.metric c).symm v = q := by
      rw [NormalCoordinates.normalChartAt_symm_apply (I := I) Y.metric c hv_tgt]
      exact hy_eq.symm
    rw [← hsymm]
    exact (NormalCoordinates.normalChartAt (I := I) Y.metric c).right_inv hv_tgt
  rw [Metric.mem_ball, dist_zero_right, hchart]
  have hsq : Real.sqrt (Y.metric.inner c v v) < expRadiusGp (I := I) Y.metric c := by
    rw [hv_len]; exact hsmall
  exact norm_lt_expMapC2Radius_of_sqrt_inner_lt (I := I) Y.metric c hsq







theorem properBallImgOfRad'
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (P : ProperMetricOn (I := I) Y) {c : Y.M} {R σ : Real}
    (hR :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space Y.M := Y.t2
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      R < expRadiusGp (I := I) Y.metric c)
    (hσ :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space Y.M := Y.t2
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      R / Real.sqrt (gpCoerciveConst (I := I) Y.metric c) < σ) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space Y.M := Y.t2
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    letI : MetricSpace Y.M := P.ms
    (NormalCoordinates.normalChartAt (I := I) Y.metric c) '' Metric.closedBall c R ⊆
      Metric.ball (0 : E) σ := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space Y.M := Y.t2
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  letI : MetricSpace Y.M := P.ms
  letI : RiemannianBundle (fun x : Y.M => TangentSpace I x) :=
    ⟨Y.metric.toRiemannianMetric⟩
  have hEnorm :
      ∀ x : Y.M, ∀ v : TangentSpace I x,
        ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (Y.metric.inner x v v)) := by
    intro x v
    simpa using
      (DifferentialGeometry.Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := I) Y.metric x v)
  rintro a ⟨q, hq, rfl⟩
  have hdist_le : dist c q ≤ R := by
    simpa [dist_comm] using (Metric.mem_closedBall.mp hq)
  have hed : riemannianEDist I c q = ENNReal.ofReal (dist c q) := by
    have h := P.realizes c q
    simpa [PointedRiemannianManifold.emetricSpace] using h
  have hfin : riemannianEDist I c q ≠ (⊤ : ℝ≥0∞) := by
    rw [hed]; exact ENNReal.ofReal_ne_top
  have hsmall : (riemannianEDist I c q).toReal < expRadiusGp (I := I) Y.metric c := by
    rw [hed, ENNReal.toReal_ofReal (dist_nonneg : 0 ≤ dist c q)]
    exact lt_of_le_of_lt hdist_le hR
  obtain ⟨v, hv_tgt, _hv_dom, hv_len, hy_eq⟩ :=
    metricBall_subset_normalBall (I := I) Y.metric c hEnorm hfin hsmall
  have hchart : NormalCoordinates.normalChartAt (I := I) Y.metric c q = v := by
    have hsymm : (NormalCoordinates.normalChartAt (I := I) Y.metric c).symm v = q := by
      rw [NormalCoordinates.normalChartAt_symm_apply (I := I) Y.metric c hv_tgt]
      exact hy_eq.symm
    rw [← hsymm]
    exact (NormalCoordinates.normalChartAt (I := I) Y.metric c).right_inv hv_tgt
  rw [Metric.mem_ball, dist_zero_right, hchart]
  have hcoerc : 0 < gpCoerciveConst (I := I) Y.metric c := gpCoerciveConst_pos (I := I) Y.metric c
  have hsc : 0 < Real.sqrt (gpCoerciveConst (I := I) Y.metric c) := Real.sqrt_pos.mpr hcoerc
  have hcle : gpCoerciveConst (I := I) Y.metric c * ‖v‖ ^ 2 ≤ Y.metric.inner c v v :=
    gpCoerciveConst_le (I := I) Y.metric c v
  have hsqrt_le :
      Real.sqrt (gpCoerciveConst (I := I) Y.metric c) * ‖v‖ ≤
        Real.sqrt (Y.metric.inner c v v) := by
    have hrw : Real.sqrt (gpCoerciveConst (I := I) Y.metric c) * ‖v‖
        = Real.sqrt (gpCoerciveConst (I := I) Y.metric c * ‖v‖ ^ 2) := by
      rw [Real.sqrt_mul (le_of_lt hcoerc), Real.sqrt_sq (norm_nonneg v)]
    rw [hrw]
    exact Real.sqrt_le_sqrt hcle
  have hgc_le : Real.sqrt (Y.metric.inner c v v) ≤ R := by
    rw [hv_len, hed, ENNReal.toReal_ofReal (dist_nonneg : 0 ≤ dist c q)]
    exact hdist_le
  have hbound : ‖v‖ ≤ R / Real.sqrt (gpCoerciveConst (I := I) Y.metric c) := by
    rw [le_div_iff₀ hsc]
    calc ‖v‖ * Real.sqrt (gpCoerciveConst (I := I) Y.metric c)
        = Real.sqrt (gpCoerciveConst (I := I) Y.metric c) * ‖v‖ := by ring
      _ ≤ Real.sqrt (Y.metric.inner c v v) := hsqrt_le
      _ ≤ R := hgc_le
  exact lt_of_le_of_lt hbound hσ





theorem hatCageImg (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : forall k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P)
    (pb : hd.PackingBound D) (r : Real) (n : Nat)
    (center : Fin (pb.A r) -> (X.obj (L.φ n)).M) (gamma : Fin (pb.A r))
    (hcenter : seqCenter hd D P (L.φ n) (gamma : Nat) = some (center gamma))
    (hR :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      4 * L.lamInf (gamma : Nat) <
        expRadiusGp (I := I) (X.obj (L.φ n)).metric (center gamma)) :
    letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
    letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
    letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
    letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
    letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
      (X.obj (L.φ n)).t2TangentBundle
    letI : MetricSpace (X.obj (L.φ n)).M := (P (L.φ n)).ms
    (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric (center gamma)) ''
        NetLimitData.hatSourceCage (I := I) (X := X) hd P L pb r n gamma ⊆
      Metric.ball (0 : E)
        (expMapC2Radius (I := I) (X.obj (L.φ n)).metric (center gamma)) := by
  letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
  letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
  letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
  letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
  letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
    (X.obj (L.φ n)).t2TangentBundle
  letI : MetricSpace (X.obj (L.φ n)).M := (P (L.φ n)).ms
  refine Set.Subset.trans
    (Set.image_mono
      (NetLimitData.hatCageInClosed (I := I) (X := X) hd P L pb r n gamma hcenter)) ?_
  exact properBallImgOfRad (I := I) (X.obj (L.φ n)) (P (L.φ n))
    (c := center gamma) (R := 4 * L.lamInf (gamma : Nat)) hR









theorem hatCageImg' (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : forall k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P)
    (pb : hd.PackingBound D) (r : Real) (n : Nat)
    (center : Fin (pb.A r) -> (X.obj (L.φ n)).M) (gamma : Fin (pb.A r))
    (sigma : Fin (pb.A r) -> Real)
    (hcenter : seqCenter hd D P (L.φ n) (gamma : Nat) = some (center gamma))
    (hR :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      4 * L.lamInf (gamma : Nat) <
        expRadiusGp (I := I) (X.obj (L.φ n)).metric (center gamma))
    (hσ :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      4 * L.lamInf (gamma : Nat) /
          Real.sqrt (gpCoerciveConst (I := I) (X.obj (L.φ n)).metric (center gamma)) <
        sigma gamma) :
    letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
    letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
    letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
    letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
    letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
      (X.obj (L.φ n)).t2TangentBundle
    letI : MetricSpace (X.obj (L.φ n)).M := (P (L.φ n)).ms
    (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric (center gamma)) ''
        NetLimitData.hatSourceCage (I := I) (X := X) hd P L pb r n gamma ⊆
      Metric.ball (0 : E) (sigma gamma) := by
  letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
  letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
  letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
  letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
  letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
    (X.obj (L.φ n)).t2TangentBundle
  letI : MetricSpace (X.obj (L.φ n)).M := (P (L.φ n)).ms
  refine Set.Subset.trans
    (Set.image_mono
      (NetLimitData.hatCageInClosed (I := I) (X := X) hd P L pb r n gamma hcenter)) ?_
  exact properBallImgOfRad' (I := I) (X.obj (L.φ n)) (P (L.φ n))
    (c := center gamma) (R := 4 * L.lamInf (gamma : Nat)) (σ := sigma gamma) hR hσ







theorem hUx_of_sigma (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : forall k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P)
    (pb : hd.PackingBound D) (r : Real)
    (x : Fin (pb.A r) -> forall k : Nat, (X.obj (L.φ k)).M) (σ : Fin (pb.A r) -> Real)
    (hσ : forall gamma : Fin (pb.A r), forall k : Nat,
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) := (X.obj (L.φ k)).t2TangentBundle
      σ gamma ≤ expMapC2Radius (I := I) (X.obj (L.φ k)).metric (x gamma k)) :
    forall gamma : Fin (pb.A r), forall k : Nat,
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) := (X.obj (L.φ k)).t2TangentBundle
      Metric.ball (0 : E) (σ gamma) ⊆
        Metric.ball (0 : E) (expMapC2Radius (I := I) (X.obj (L.φ k)).metric (x gamma k)) := by
  intro gamma k
  exact Metric.ball_subset_ball (hσ gamma k)


def SigmaScaleAt (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : forall k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P)
    (pb : hd.PackingBound D) (r : Real)
    (x : Fin (pb.A r) -> forall k : Nat, (X.obj (L.φ k)).M)
    (σ : Fin (pb.A r) -> Real) (n : Nat) : Prop :=
  forall gamma : Fin (pb.A r),
    letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
    letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
    letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
    letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
    letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
      (X.obj (L.φ n)).t2TangentBundle
    4 * L.lamInf (gamma : Nat) /
        Real.sqrt (gpCoerciveConst (I := I) (X.obj (L.φ n)).metric (x gamma n)) < σ gamma ∧
      σ gamma ≤ expMapC2Radius (I := I) (X.obj (L.φ n)).metric (x gamma n)



def SigmaScaleTail (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : forall k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P)
    (pb : hd.PackingBound D) (r : Real)
    (x : Fin (pb.A r) -> forall k : Nat, (X.obj (L.φ k)).M)
    (σ : Fin (pb.A r) -> Real) : Prop :=
  ∀ᶠ n in Filter.atTop, SigmaScaleAt (I := I) hd P L pb r x σ n








def SigmaScaleField (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : forall k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P)
    (pb : hd.PackingBound D) (r : Real)
    (x : Fin (pb.A r) -> forall k : Nat, (X.obj (L.φ k)).M) (σ : Fin (pb.A r) -> Real) : Prop :=
  forall gamma : Fin (pb.A r), forall k : Nat,
    letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
    letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
    letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
    letI : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
    letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) := (X.obj (L.φ k)).t2TangentBundle
    4 * L.lamInf (gamma : Nat) /
        Real.sqrt (gpCoerciveConst (I := I) (X.obj (L.φ k)).metric (x gamma k)) < σ gamma ∧
      σ gamma ≤ expMapC2Radius (I := I) (X.obj (L.φ k)).metric (x gamma k)


theorem SigmaScaleField.at {hd : InjRadiusDecayInput (I := I) X} {D : Real}
    {P : forall k : Nat, ProperMetricOn (I := I) (X.obj k)}
    {L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P}
    {pb : hd.PackingBound D} {r : Real}
    {x : Fin (pb.A r) -> forall k : Nat, (X.obj (L.φ k)).M}
    {σ : Fin (pb.A r) -> Real}
    (hfield : SigmaScaleField (I := I) hd P L pb r x σ) (n : Nat) :
    SigmaScaleAt (I := I) hd P L pb r x σ n := fun gamma => hfield gamma n


theorem SigmaScaleField.to_tail {hd : InjRadiusDecayInput (I := I) X} {D : Real}
    {P : forall k : Nat, ProperMetricOn (I := I) (X.obj k)}
    {L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P}
    {pb : hd.PackingBound D} {r : Real}
    {x : Fin (pb.A r) -> forall k : Nat, (X.obj (L.φ k)).M}
    {σ : Fin (pb.A r) -> Real}
    (hfield : SigmaScaleField (I := I) hd P L pb r x σ) :
    SigmaScaleTail (I := I) hd P L pb r x σ :=
  Filter.Eventually.of_forall hfield.at


theorem SigmaScaleTail.subseq {hd : InjRadiusDecayInput (I := I) X} {D : Real}
    {P : forall k : Nat, ProperMetricOn (I := I) (X.obj k)}
    (L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P)
    (pb : hd.PackingBound D) (r : Real)
    {x : Fin (pb.A r) -> forall k : Nat, (X.obj (L.φ k)).M}
    {σ : Fin (pb.A r) -> Real}
    (htail : SigmaScaleTail (I := I) hd P L pb r x σ)
    {ψ : Nat → Nat} (hψ : StrictMono ψ) :
    SigmaScaleTail (I := I) hd P (L.subseq hψ) pb r
      (fun gamma k => x gamma (ψ k)) σ := by
  filter_upwards [hψ.tendsto_atTop.eventually htail] with n hn
  intro gamma
  exact hn gamma



theorem SigmaScaleTail.exists_field
    {hd : InjRadiusDecayInput (I := I) X} {D : Real}
    {P : forall k : Nat, ProperMetricOn (I := I) (X.obj k)}
    (L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P)
    (pb : hd.PackingBound D) (r : Real)
    {x : Fin (pb.A r) -> forall k : Nat, (X.obj (L.φ k)).M}
    {σ : Fin (pb.A r) -> Real}
    (htail : SigmaScaleTail (I := I) hd P L pb r x σ) :
    ∃ ψ : Nat → Nat, ∃ hψ : StrictMono ψ,
      SigmaScaleField (I := I) hd P (L.subseq hψ) pb r
        (fun gamma k => x gamma (ψ k)) σ := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp htail
  let ψ : Nat → Nat := fun k => k + N
  have hψ : StrictMono ψ := by
    simpa only [ψ] using strictMono_id.add_const N
  refine ⟨ψ, hψ, ?_⟩
  intro gamma k
  exact hN (ψ k) (by simp only [ψ]; omega) gamma



theorem SigmaScaleField.expRadiusGp {hd : InjRadiusDecayInput (I := I) X} {D : Real}
    {P : forall k : Nat, ProperMetricOn (I := I) (X.obj k)}
    {L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P}
    {pb : hd.PackingBound D} {r : Real}
    {x : Fin (pb.A r) -> forall k : Nat, (X.obj (L.φ k)).M} {σ : Fin (pb.A r) -> Real}
    (hfield : SigmaScaleField (I := I) hd P L pb r x σ)
    (gamma : Fin (pb.A r)) (k : Nat) :
    letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
    letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
    letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
    letI : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
    letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) := (X.obj (L.φ k)).t2TangentBundle
    4 * L.lamInf (gamma : Nat) <
      expRadiusGp (I := I) (X.obj (L.φ k)).metric (x gamma k) := by
  letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
  letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
  letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
  letI : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
  letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) := (X.obj (L.φ k)).t2TangentBundle
  obtain ⟨hlo, hhi⟩ := hfield gamma k
  have hsc : 0 < Real.sqrt (gpCoerciveConst (I := I) (X.obj (L.φ k)).metric (x gamma k)) :=
    Real.sqrt_pos.mpr (gpCoerciveConst_pos (I := I) (X.obj (L.φ k)).metric (x gamma k))
  have h1 : 4 * L.lamInf (gamma : Nat) /
      Real.sqrt (gpCoerciveConst (I := I) (X.obj (L.φ k)).metric (x gamma k)) <
      expMapC2Radius (I := I) (X.obj (L.φ k)).metric (x gamma k) := lt_of_lt_of_le hlo hhi
  rw [div_lt_iff₀ hsc] at h1
  exact h1.trans_eq (mul_comm _ _)



theorem NormalRadiusProfile.sigmaCenterTail
    {hd : InjRadiusDecayInput (I := I) X}
    {hb : NormalCoordMetricBoundInput (I := I) X}
    (h : NormalRadiusProfile hd hb) {D : Real} (hD : 0 < D)
    (h16 : (16 : Real) < h.ratio * D)
    (P : forall k : Nat, ProperMetricOn (I := I) (X.obj k))
    (hre : hd.RealizesEdist)
    (L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P)
    (pb : hd.PackingBound D) (r : Real) :
    SigmaScaleTail (I := I) hd P L pb r
      (fun gamma k => seqCenterD hd P L k (gamma : Nat))
      (fun gamma => 8 * L.lamInf (gamma : Nat)) := by
  have hwin : ∀ᶠ n in Filter.atTop, ∀ gamma ∈ Finset.range (pb.A r),
      L.lamInf gamma / 2 ≤
        hd.lambda D (seqRadius hd D P (L.φ n) gamma) :=
    (Filter.eventually_all_finset _).mpr fun gamma _ =>
      (L.lambda_window hd hD P gamma).mono fun _ hgamma => by
        simpa only [NetLimitData.lamInf] using hgamma.1
  filter_upwards [hwin] with n hn
  intro gamma
  letI : MetricSpace (X.obj (L.φ n)).M := (P (L.φ n)).ms
  haveI : ProperSpace (X.obj (L.φ n)).M := (P (L.φ n)).proper
  have hx : hd.dist (L.φ n) (seqCenterD hd P L n (gamma : Nat))
      (X.obj (L.φ n)).basepoint ≤
      seqRadius hd D P (L.φ n) (gamma : Nat) := by
    rw [← ProperMetricOn.dist_eq hd hre P (L.φ n),
      ← seqCenterD_dist_eq hd P L n (gamma : Nat)]
  letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
  letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
  letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
  letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
  letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
    (X.obj (L.φ n)).t2TangentBundle
  constructor
  · have hhalf : (1 / 2 : Real) ≤ gpCoerciveConst (I := I)
        (X.obj (L.φ n)).metric (seqCenterD hd P L n (gamma : Nat)) :=
      hb.half_le_gpConst (L.φ n) (seqCenterD hd P L n (gamma : Nat))
    have hsqrt_half : (1 / 2 : Real) < Real.sqrt (1 / 2 : Real) := by
      have hs := Real.sq_sqrt (by norm_num : (0 : Real) ≤ 1 / 2)
      have hn := Real.sqrt_nonneg (1 / 2 : Real)
      nlinarith
    have hsqrt : (1 / 2 : Real) < Real.sqrt (gpCoerciveConst (I := I)
        (X.obj (L.φ n)).metric (seqCenterD hd P L n (gamma : Nat))) :=
      hsqrt_half.trans_le (Real.sqrt_le_sqrt hhalf)
    have hsc : 0 < Real.sqrt (gpCoerciveConst (I := I)
        (X.obj (L.φ n)).metric (seqCenterD hd P L n (gamma : Nat))) :=
      Real.sqrt_pos.mpr (gpCoerciveConst_pos (I := I)
        (X.obj (L.φ n)).metric (seqCenterD hd P L n (gamma : Nat)))
    have hlam : 0 < L.lamInf (gamma : Nat) :=
      hd.lambda_pos hD (L.rInf (gamma : Nat))
    apply (div_lt_iff₀ hsc).2
    have hfour : (4 : Real) < 8 * Real.sqrt (gpCoerciveConst (I := I)
        (X.obj (L.φ n)).metric (seqCenterD hd P L n (gamma : Nat))) := by
      nlinarith
    calc
      4 * L.lamInf (gamma : Nat) <
          (8 * Real.sqrt (gpCoerciveConst (I := I)
            (X.obj (L.φ n)).metric
              (seqCenterD hd P L n (gamma : Nat)))) *
            L.lamInf (gamma : Nat) :=
        mul_lt_mul_of_pos_right hfour hlam
      _ = (8 * L.lamInf (gamma : Nat)) *
          Real.sqrt (gpCoerciveConst (I := I) (X.obj (L.φ n)).metric
            (seqCenterD hd P L n (gamma : Nat))) := by ring
  · calc
      8 * L.lamInf (gamma : Nat) =
          16 * (L.lamInf (gamma : Nat) / 2) := by ring
      _ ≤ 16 * hd.lambda D
          (seqRadius hd D P (L.φ n) (gamma : Nat)) :=
        mul_le_mul_of_nonneg_left
          (hn (gamma : Nat) (Finset.mem_range.mpr gamma.isLt)) (by norm_num)
      _ ≤ expMapC2Radius (I := I) (X.obj (L.φ n)).metric
          (seqCenterD hd P L n (gamma : Nat)) :=
        (h.mul_lambda_lt_exp (D := D) (c := 16)
          (R := seqRadius hd D P (L.φ n) (gamma : Nat)) hD h16 hx).le




omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E] in
theorem binfMemClosed {U V' : Set E} {B : Nat -> E -> E} {Binf : E -> E}
    (hB : MapCInfConvOnCompacts U B Binf) {v : E} (hv : v ∈ U)
    (hV'closed : IsClosed V') (hmem : ∀ᶠ a in Filter.atTop, B a v ∈ V') :
    Binf v ∈ V' :=
  hV'closed.mem_of_tendsto (tendsto_of_cInf hB hv) hmem





theorem HasAtomWeightLim.binf_of_live
    (inp : MetricCompactnessInputs (I := I) X)
    (hradD : 2 * item3RadiusFactor inp.decay inp.D < inp.D)
    (hradRatio : 2 * item3RadiusFactor inp.decay inp.D <
      inp.normalRadius.ratio * inp.D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) (r : Real) (hr : 0 ≤ r)
    (hgp : Item3GpScaleTail (I := I) inp.decay inp.D P L inp.pack r)
    (alpha : LiveSlot L inp.pack r) (U : Set E)
    (aInf : Fin (inp.pack.A r) → E → Real)
    (hlim : HasAtomWeightLim (I := I) inp.decay inp.hD P L inp.realizes
      inp.pack r hr
      (fun k => seqCenterD inp.decay P L k (alpha.1 : Nat)) U aInf)
    (phi : Nat -> Nat) (hphi : StrictMono phi)
    (gamma : LiveSlot L inp.pack r)
    (Binf : E -> E)
    (hB : MapCInfConvOnCompacts U
      (fun k => normalTransition (I := I) (X.obj (L.φ (phi k)))
        (seqCenterD inp.decay P L (phi k) (alpha.1 : Nat))
        (seqCenterD inp.decay P L (phi k) (gamma.1 : Nat)))
      Binf)
    {z : E} (hz : z ∈ U)
    (hweight : rawWeights
      (cutRaw (aInf (baseIndex inp.decay inp.realizes inp.pack hr)) aInf
        (baseIndex inp.decay inp.realizes inp.pack hr)) z gamma.1 ≠ 0) :
    Binf z ∈ Metric.closedBall 0 (6 * L.lamInf (gamma.1 : Nat)) := by
  have hweightTail := hphi.tendsto_atTop.eventually
    (hlim.weight_ne_tail hz hweight)
  have hrad : Item3RadiusTail (I := I) inp.decay inp.D P L inp.pack r
      (item3RadiusFactor inp.decay inp.D) :=
    inp.normalRadius.radiusScaleTail inp.hD
      (item3Factor_pos inp.decay inp.D) hradD hradRatio
      P inp.realizes L inp.pack r
  have hradTail := hphi.tendsto_atTop.eventually hrad
  have hgpTail := hphi.tendsto_atTop.eventually hgp
  have hcenterTail := hphi.tendsto_atTop.eventually
    (seqCenterD_live inp.decay P L (gamma.1 : Nat) gamma.2)
  have hmem : ∀ᶠ k in Filter.atTop,
      normalTransition (I := I) (X.obj (L.φ (phi k)))
          (seqCenterD inp.decay P L (phi k) (alpha.1 : Nat))
          (seqCenterD inp.decay P L (phi k) (gamma.1 : Nat)) z ∈
        Metric.closedBall 0 (6 * L.lamInf (gamma.1 : Nat)) := by
    filter_upwards [hweightTail, hradTail, hgpTail, hcenterTail]
      with k hweightK hradK hgpK hcenterK
    letI : TopologicalSpace (X.obj (L.φ (phi k))).M :=
      (X.obj (L.φ (phi k))).topology
    letI : ChartedSpace H (X.obj (L.φ (phi k))).M :=
      (X.obj (L.φ (phi k))).charted
    letI : IsManifold I ∞ (X.obj (L.φ (phi k))).M :=
      (X.obj (L.φ (phi k))).smooth
    letI : T2Space (TangentBundle I (X.obj (L.φ (phi k))).M) :=
      (X.obj (L.φ (phi k))).t2TangentBundle
    have hExp : (1 : Real) ≤
        Real.exp (inp.decay.C * (20 * inp.decay.lambda inp.D 0)) := by
      rw [show (1 : Real) = Real.exp 0 from Real.exp_zero.symm]
      exact Real.exp_le_exp.mpr
        (mul_nonneg inp.decay.C_nonneg
          (by nlinarith [(inp.decay.lambda_pos inp.hD 0).le]))
    have hfactor : (8 : Real) ≤ item3RadiusFactor inp.decay inp.D := by
      rw [item3RadiusFactor]
      nlinarith
    have hC2 : 8 * L.lamInf (gamma.1 : Nat) ≤
        expMapC2Radius (I := I) (X.obj (L.φ (phi k))).metric
          (seqCenterD inp.decay P L (phi k) (gamma.1 : Nat)) :=
      (mul_le_mul_of_nonneg_right hfactor
        (inp.decay.lambda_pos inp.hD (L.rInf (gamma.1 : Nat))).le).trans
          (hradK gamma.1
            (seqCenterD inp.decay P L (phi k) (gamma.1 : Nat)) hcenterK).2
    exact Metric.ball_subset_closedBall
      (inp.weight_trans_small P L r (phi k) hgpK
        (fun j => seqCenterD inp.decay P L j (alpha.1 : Nat))
        (baseIndex inp.decay inp.realizes inp.pack hr) gamma.1 hC2 z hweightK)
  exact binfMemClosed hB hz Metric.isClosed_closedBall hmem


theorem HasAtomWeightLim.binf_of_slot
    (inp : MetricCompactnessInputs (I := I) X)
    (hradD : 2 * item3RadiusFactor inp.decay inp.D < inp.D)
    (hradRatio : 2 * item3RadiusFactor inp.decay inp.D <
      inp.normalRadius.ratio * inp.D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) (r : Real) (hr : 0 ≤ r)
    (hgp : Item3GpScaleTail (I := I) inp.decay inp.D P L inp.pack r)
    (alpha : LiveSlot L inp.pack r) (U : Set E)
    (aInf : Fin (inp.pack.A r) → E → Real)
    (hlim : HasAtomWeightLim (I := I) inp.decay inp.hD P L inp.realizes
      inp.pack r hr
      (fun k => seqCenterD inp.decay P L k (alpha.1 : Nat)) U aInf)
    (phi : Nat -> Nat) (hphi : StrictMono phi)
    (target : InterSlot L inp.pack r alpha)
    (Binf : InterSlot L inp.pack r alpha -> E -> E)
    (hB : MapCInfConvOnCompacts U
      (fun k => normalTransition (I := I) (X.obj (L.φ (phi k)))
        (seqCenterD inp.decay P L (phi k) (alpha.1 : Nat))
        (seqCenterD inp.decay P L (phi k) (target.1.1 : Nat)))
      (Binf target))
    {z : E} (hz : z ∈ U)
    (hweight : rawWeights
      (cutRaw (aInf (baseIndex inp.decay inp.realizes inp.pack hr)) aInf
        (baseIndex inp.decay inp.realizes inp.pack hr)) z target.1.1 ≠ 0) :
    Binf target z ∈
      Metric.closedBall 0 (6 * L.lamInf (target.1.1 : Nat)) := by
  exact hlim.binf_of_live inp hradD hradRatio P L r hr hgp alpha U aInf
    phi hphi target.1 (Binf target) hB hz hweight



theorem HasAtomWeightLim.binf_of_weight
    (inp : MetricCompactnessInputs (I := I) X)
    (hradD : 2 * item3RadiusFactor inp.decay inp.D < inp.D)
    (hradRatio : 2 * item3RadiusFactor inp.decay inp.D <
      inp.normalRadius.ratio * inp.D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) (r : Real) (hr : 0 ≤ r)
    (hgp : Item3GpScaleTail (I := I) inp.decay inp.D P L inp.pack r)
    (alpha : LiveSlot L inp.pack r) (U : Set E)
    (aInf : Fin (inp.pack.A r) → E → Real)
    (hlim : HasAtomWeightLim (I := I) inp.decay inp.hD P L inp.realizes
      inp.pack r hr
      (fun k => seqCenterD inp.decay P L k (alpha.1 : Nat)) U aInf)
    (hsource : ∀ᶠ k in Filter.atTop,
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
        (X.obj (L.φ k)).t2TangentBundle
      Set.MapsTo
        (fun z => expMapDiffeo (I := I) (X.obj (L.φ k)).metric
          (seqCenterD inp.decay P L k (alpha.1 : Nat)) z)
        U (L.hatBall inp.decay inp.D P inp.pack r k alpha.1))
    (phi : Nat -> Nat) (hphi : StrictMono phi)
    (Binf : InterSlot L inp.pack r alpha -> E -> E)
    (hB : forall target : InterSlot L inp.pack r alpha,
      MapCInfConvOnCompacts U
        (fun k => normalTransition (I := I) (X.obj (L.φ (phi k)))
          (seqCenterD inp.decay P L (phi k) (alpha.1 : Nat))
          (seqCenterD inp.decay P L (phi k) (target.1.1 : Nat)))
        (Binf target))
    {z : E} (hz : z ∈ U) (gamma : Fin (inp.pack.A r))
    (hweight : rawWeights
      (cutRaw (aInf (baseIndex inp.decay inp.realizes inp.pack hr)) aInf
        (baseIndex inp.decay inp.realizes inp.pack hr)) z gamma ≠ 0) :
    ∃ target : InterSlot L inp.pack r alpha,
      target.1.1 = gamma ∧
        Binf target z ∈ Metric.closedBall 0 (6 * L.lamInf (gamma : Nat)) := by
  classical
  have hdata := hlim
  dsimp only [HasAtomWeightLim] at hdata
  have hgammaLive : L.alive (gamma : Nat) = true := by
    cases hgamma : L.alive (gamma : Nat) with
    | false =>
        have haZero : aInf gamma = 0 := hdata.1 gamma hgamma
        have hnum : aInf gamma z ≠ 0 :=
          num_ne_of_cut_ne (num_ne_of_raw_ne hweight)
        exact False.elim (hnum (by rw [haZero]; rfl))
    | true => rfl
  have hinter : ∀ᶠ k in Filter.atTop,
      BInter inp.decay inp.D P L.lamInf
        (alpha.1 : Nat) (gamma : Nat) (L.φ k) :=
    hlim.binter_of_weight hgp alpha.1 gamma hz hsource hweight
  let target : InterSlot L inp.pack r alpha :=
    ⟨⟨gamma, hgammaLive⟩, hinter⟩
  refine ⟨target, rfl, ?_⟩
  simpa only [target] using
    (hlim.binf_of_slot inp hradD hradRatio P L r hr hgp alpha U aInf
      phi hphi target Binf (hB target) hz (by simpa only [target] using hweight))




theorem MetricCompactnessInputs.exists_supp_trans
    (inp : MetricCompactnessInputs (I := I) X)
    (hradD : 2 * item3RadiusFactor inp.decay inp.D < inp.D)
    (hradRatio : 2 * item3RadiusFactor inp.decay inp.D <
      inp.normalRadius.ratio * inp.D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) (r : Real) (hr : 0 ≤ r)
    (hgp : Item3GpScaleTail (I := I) inp.decay inp.D P L inp.pack r)
    (alpha : LiveSlot L inp.pack r) (U : Set E)
    (hUsub : U ⊆ Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat)))
    (aInf : Fin (inp.pack.A r) → E → Real)
    (hlim : HasAtomWeightLim (I := I) inp.decay inp.hD P L inp.realizes
      inp.pack r hr
      (fun k => seqCenterD inp.decay P L k (alpha.1 : Nat)) U aInf)
    (hsource : ∀ᶠ k in Filter.atTop,
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
        (X.obj (L.φ k)).t2TangentBundle
      Set.MapsTo
        (fun z => expMapDiffeo (I := I) (X.obj (L.φ k)).metric
          (seqCenterD inp.decay P L k (alpha.1 : Nat)) z)
        U (L.hatBall inp.decay inp.D P inp.pack r k alpha.1)) :
    ∃ phi : Nat -> Nat, StrictMono phi ∧
      ∃ Jinf : InterSlot L inp.pack r alpha -> E -> E,
      ∃ Jbarinf : InterSlot L inp.pack r alpha -> E -> E,
        (forall target : InterSlot L inp.pack r alpha,
          ContDiffOn Real (⊤ : ℕ∞) (Jinf target)
              (Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat))) ∧
          ContDiffOn Real (⊤ : ℕ∞) (Jbarinf target)
              (Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat))) ∧
          ContinuousOn (Jinf target)
              (Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat))) ∧
          ContinuousOn (Jbarinf target)
              (Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat))) ∧
          MapCInfConvOnCompacts
            (Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat)))
            (fun k => normalTransition (I := I) (X.obj (L.φ (phi k)))
              (seqCenterD inp.decay P L (phi k) (alpha.1 : Nat))
              (seqCenterD inp.decay P L (phi k) (target.1.1 : Nat)))
            (Jinf target) ∧
          MapCInfConvOnCompacts
            (Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat)))
            (fun k => normalTransition (I := I) (X.obj (L.φ (phi k)))
              (seqCenterD inp.decay P L (phi k) (target.1.1 : Nat))
              (seqCenterD inp.decay P L (phi k) (alpha.1 : Nat)))
            (Jbarinf target) ∧
          (forall z, z ∈ Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat)) ->
            Jinf target z ∈ Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat)) ->
              Jbarinf target (Jinf target z) = z) ∧
          (forall w, w ∈ Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat)) ->
            Jbarinf target w ∈ Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat)) ->
              Jinf target (Jbarinf target w) = w)) ∧
        forall z : E, z ∈ U -> forall gamma : Fin (inp.pack.A r),
          rawWeights
            (cutRaw (aInf (baseIndex inp.decay inp.realizes inp.pack hr)) aInf
              (baseIndex inp.decay inp.realizes inp.pack hr)) z gamma ≠ 0 ->
            ∃ target : InterSlot L inp.pack r alpha,
              target.1.1 = gamma ∧
                Jinf target z ∈
                  Metric.closedBall 0 (6 * L.lamInf (gamma : Nat)) := by
  classical
  letI : Finite (InterSlot L inp.pack r alpha) :=
    Finite.of_injective
      (fun target : InterSlot L inp.pack r alpha => target.1.1)
      (by
        intro a b hab
        apply Subtype.ext
        apply Subtype.ext
        exact hab)
  obtain ⟨phi, hphi, Jinf, Jbarinf, hspec⟩ :=
    inp.exists_pair_trans hradD hradRatio P L r
      (fun _ : InterSlot L inp.pack r alpha => alpha)
      (fun target : InterSlot L inp.pack r alpha => target.1)
      (fun target : InterSlot L inp.pack r alpha => target.2)
  refine ⟨phi, hphi, Jinf, Jbarinf, hspec, ?_⟩
  intro z hz gamma hweight
  exact hlim.binf_of_weight inp hradD hradRatio P L r hr hgp alpha U aInf
    hsource phi hphi Jinf (fun target K hK hKU p =>
      (hspec target).2.2.2.2.1 K hK (hKU.trans hUsub) p)
    hz gamma hweight




theorem MetricCompactnessInputs.exists_supp_fin
    (inp : MetricCompactnessInputs (I := I) X)
    (hradD : 2 * item3RadiusFactor inp.decay inp.D < inp.D)
    (hradRatio : 2 * item3RadiusFactor inp.decay inp.D <
      inp.normalRadius.ratio * inp.D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) (r : Real) (hr : 0 ≤ r)
    (hgp : Item3GpScaleTail (I := I) inp.decay inp.D P L inp.pack r)
    (U : LiveSlot L inp.pack r → Set E)
    (hUsub : ∀ alpha, U alpha ⊆
      Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat)))
    (aInf : (alpha : LiveSlot L inp.pack r) →
      Fin (inp.pack.A r) → E → Real)
    (hlim : ∀ alpha,
      HasAtomWeightLim (I := I) inp.decay inp.hD P L inp.realizes
        inp.pack r hr
        (fun k => seqCenterD inp.decay P L k (alpha.1 : Nat))
        (U alpha) (aInf alpha))
    (hsource : ∀ alpha, ∀ᶠ k in Filter.atTop,
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
        (X.obj (L.φ k)).t2TangentBundle
      Set.MapsTo
        (fun z => expMapDiffeo (I := I) (X.obj (L.φ k)).metric
          (seqCenterD inp.decay P L k (alpha.1 : Nat)) z)
        (U alpha) (L.hatBall inp.decay inp.D P inp.pack r k alpha.1)) :
    ∃ phi : Nat → Nat, StrictMono phi ∧
      ∃ Jinf : (alpha : LiveSlot L inp.pack r) →
          InterSlot L inp.pack r alpha → E → E,
      ∃ Jbarinf : (alpha : LiveSlot L inp.pack r) →
          InterSlot L inp.pack r alpha → E → E,
        (∀ alpha target,
          ContDiffOn Real (⊤ : ℕ∞) (Jinf alpha target)
              (Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat))) ∧
          ContDiffOn Real (⊤ : ℕ∞) (Jbarinf alpha target)
              (Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat))) ∧
          ContinuousOn (Jinf alpha target)
              (Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat))) ∧
          ContinuousOn (Jbarinf alpha target)
              (Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat))) ∧
          MapCInfConvOnCompacts
            (Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat)))
            (fun k => normalTransition (I := I) (X.obj (L.φ (phi k)))
              (seqCenterD inp.decay P L (phi k) (alpha.1 : Nat))
              (seqCenterD inp.decay P L (phi k) (target.1.1 : Nat)))
            (Jinf alpha target) ∧
          MapCInfConvOnCompacts
            (Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat)))
            (fun k => normalTransition (I := I) (X.obj (L.φ (phi k)))
              (seqCenterD inp.decay P L (phi k) (target.1.1 : Nat))
              (seqCenterD inp.decay P L (phi k) (alpha.1 : Nat)))
            (Jbarinf alpha target) ∧
          (∀ z, z ∈ Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat)) →
            Jinf alpha target z ∈
                Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat)) →
              Jbarinf alpha target (Jinf alpha target z) = z) ∧
          (∀ w, w ∈ Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat)) →
            Jbarinf alpha target w ∈
                Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat)) →
              Jinf alpha target (Jbarinf alpha target w) = w)) ∧
        ∀ alpha z, z ∈ U alpha → ∀ gamma : Fin (inp.pack.A r),
          rawWeights
            (cutRaw
              (aInf alpha (baseIndex inp.decay inp.realizes inp.pack hr))
              (aInf alpha) (baseIndex inp.decay inp.realizes inp.pack hr))
            z gamma ≠ 0 →
          ∃ target : InterSlot L inp.pack r alpha,
            target.1.1 = gamma ∧
              Jinf alpha target z ∈
                Metric.closedBall 0 (6 * L.lamInf (gamma : Nat)) := by
  classical
  let PairSlot := Σ alpha : LiveSlot L inp.pack r, InterSlot L inp.pack r alpha
  letI (alpha : LiveSlot L inp.pack r) : Finite (InterSlot L inp.pack r alpha) :=
    Finite.of_injective
      (fun target : InterSlot L inp.pack r alpha => target.1.1)
      (by
        intro a b hab
        apply Subtype.ext
        apply Subtype.ext
        exact hab)
  letI : Finite PairSlot := inferInstance
  obtain ⟨phi, hphi, J, Jbar, hspec⟩ :=
    inp.exists_pair_trans hradD hradRatio P L r
      (fun pair : PairSlot => pair.1)
      (fun pair : PairSlot => pair.2.1)
      (fun pair : PairSlot => pair.2.2)
  let Jinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E :=
    fun alpha target => J ⟨alpha, target⟩
  let Jbarinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E :=
    fun alpha target => Jbar ⟨alpha, target⟩
  refine ⟨phi, hphi, Jinf, Jbarinf, ?_, ?_⟩
  · intro alpha target
    exact hspec ⟨alpha, target⟩
  · intro alpha z hz gamma hweight
    exact (hlim alpha).binf_of_weight inp hradD hradRatio P L r hr hgp
      alpha (U alpha) (aInf alpha) (hsource alpha) phi hphi (Jinf alpha)
      (fun target K hK hKU p =>
        (hspec ⟨alpha, target⟩).2.2.2.2.1 K hK
          (hKU.trans (hUsub alpha)) p)
      hz gamma hweight



noncomputable def interSlot?
    {hd : InjRadiusDecayInput (I := I) X} {D : Real}
    {P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k)}
    {L : NetLimitData hd D P} {pb : hd.PackingBound D} {r : Real}
    (alpha : LiveSlot L pb r) (gamma : Fin (pb.A r)) :
    Option (InterSlot L pb r alpha) := by
  classical
  exact
    if h : ∃ target : InterSlot L pb r alpha, target.1.1 = gamma then
      some (Classical.choose h)
    else
      none




noncomputable def totalPts
    {M : Type u}
    {hd : InjRadiusDecayInput (I := I) X} {D : Real}
    {P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k)}
    {L : NetLimitData hd D P} {pb : hd.PackingBound D} {r : Real}
    (pairPts : (alpha : LiveSlot L pb r) →
      InterSlot L pb r alpha → Nat → Nat → M → M)
    (alpha : LiveSlot L pb r) (a b : Nat) (x : M)
    (gamma : Fin (pb.A r)) : M :=
  match interSlot? alpha gamma with
  | some target => pairPts alpha target a b x
  | none => x



omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
@[simp] theorem activeFill_totalPts_zero
    {M : Type u}
    {hd : InjRadiusDecayInput (I := I) X} {D : Real}
    {P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k)}
    {L : NetLimitData hd D P} {pb : hd.PackingBound D} {r : Real}
    (mu : M → Fin (pb.A r) → Real)
    (pairPts : (alpha : LiveSlot L pb r) →
      InterSlot L pb r alpha → Nat → Nat → M → M)
    (alpha : LiveSlot L pb r) (a b : Nat) (x : M)
    (gamma : Fin (pb.A r)) (hzero : mu x gamma = 0) :
    centerAverage.activeFill mu (totalPts pairPts alpha a b)
        (fun y => y) x gamma = x := by
  simp [centerAverage.activeFill, hzero]




omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem activeFill_totalPts_of_ne
    {M : Type u}
    {hd : InjRadiusDecayInput (I := I) X} {D : Real}
    {P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k)}
    {L : NetLimitData hd D P} {pb : hd.PackingBound D} {r : Real}
    (mu : M → Fin (pb.A r) → Real)
    (pairPts : (alpha : LiveSlot L pb r) →
      InterSlot L pb r alpha → Nat → Nat → M → M)
    (alpha : LiveSlot L pb r) (a b : Nat) (x : M)
    (gamma : Fin (pb.A r))
    (hslot : mu x gamma ≠ 0 →
      ∃ target : InterSlot L pb r alpha, target.1.1 = gamma)
    (hne : mu x gamma ≠ 0) :
    ∃ target : InterSlot L pb r alpha,
      target.1.1 = gamma ∧
        centerAverage.activeFill mu (totalPts pairPts alpha a b)
            (fun y => y) x gamma = pairPts alpha target a b x := by
  classical
  obtain ⟨target, htarget⟩ := hslot hne
  have hexists :
      ∃ target' : InterSlot L pb r alpha, target'.1.1 = gamma :=
    ⟨target, htarget⟩
  have hlookup : interSlot? alpha gamma = some target := by
    unfold interSlot?
    split
    next h =>
      congr 1
      apply Subtype.ext
      apply Subtype.ext
      exact (Classical.choose_spec h).trans htarget.symm
    next h =>
      exact (h hexists).elim
  refine ⟨target, htarget, ?_⟩
  simp [centerAverage.activeFill, hne, totalPts, hlookup]

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 100000 in



theorem MetricCompactnessInputs.exists_atom_supp_fin
    (inp : MetricCompactnessInputs (I := I) X)
    (h8 : (8 : Real) < inp.normalRadius.gpRatio * inp.D)
    (hradD : 2 * item3RadiusFactor inp.decay inp.D < inp.D)
    (hradRatio : 2 * item3RadiusFactor inp.decay inp.D <
      inp.normalRadius.ratio * inp.D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P)
    (hstable : ∀ a b : Nat,
      (∀ᶠ k in Filter.atTop,
        BInter inp.decay inp.D P L.lamInf a b (L.φ k)) ∨
      (∀ᶠ k in Filter.atTop,
        ¬ BInter inp.decay inp.D P L.lamInf a b (L.φ k)))
    (r : Real) (hr : 0 ≤ r) :
    ∃ (phi : Nat → Nat) (hphi : StrictMono phi)
        (U : LiveSlot L inp.pack r → Set E)
        (C0 C1 : LiveSlot L inp.pack r → Set E)
        (aInf : (alpha : LiveSlot L inp.pack r) →
          Fin (inp.pack.A r) → E → Real)
        (Jinf : (alpha : LiveSlot L inp.pack r) →
          InterSlot L inp.pack r alpha → E → E)
        (Jbarinf : (alpha : LiveSlot L inp.pack r) →
          InterSlot L inp.pack r alpha → E → E),
      let Lphi := L.subseq hphi
      (∀ alpha, IsOpen (U alpha)) ∧
      (∀ alpha, U alpha ⊆
        Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat))) ∧
      (∀ alpha, IsCompact (C0 alpha)) ∧
      (∀ alpha, IsCompact (C1 alpha)) ∧
      (∀ alpha, C0 alpha ⊆ interior (C1 alpha)) ∧
      (∀ alpha, C1 alpha ⊆ U alpha) ∧
      (∀ alpha, Convex Real (C0 alpha)) ∧
      (∀ alpha, (0 : E) ∈ C0 alpha) ∧
      (∃ eta : LiveSlot L inp.pack r → Real,
        (∀ alpha, 0 < eta alpha) ∧
        ∀ k,
          let Y := X.obj (Lphi.φ k)
          letI : TopologicalSpace Y.M := Y.topology
          letI : ChartedSpace H Y.M := Y.charted
          letI : IsManifold I ∞ Y.M := Y.smooth
          letI : T2Space Y.M := Y.t2
          letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
          letI : MetricSpace Y.M := (P (Lphi.φ k)).ms
          ∀ y ∈ Lphi.hatSourceBall inp.decay P r k,
            ∃ (alpha : LiveSlot L inp.pack r) (z : E),
              expMapDiffeo (I := I) Y.metric
                  (seqCenterD inp.decay P Lphi k (alpha.1 : Nat)) z = y ∧
                Metric.closedBall z (eta alpha) ⊆ interior (C0 alpha)) ∧
      (∀ k,
        let Y := X.obj (Lphi.φ k)
        letI : TopologicalSpace Y.M := Y.topology
        letI : ChartedSpace H Y.M := Y.charted
        letI : IsManifold I ∞ Y.M := Y.smooth
        letI : T2Space Y.M := Y.t2
        letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
        letI : MetricSpace Y.M := (P (Lphi.φ k)).ms
        Lphi.hatSourceBall inp.decay P r k ⊆
          ⋃ alpha : LiveSlot L inp.pack r,
            (fun z => expMapDiffeo (I := I) Y.metric
              (seqCenterD inp.decay P Lphi k (alpha.1 : Nat)) z) ''
                interior (C0 alpha)) ∧
      (∀ k,
        let Y := X.obj (Lphi.φ k)
        letI : TopologicalSpace Y.M := Y.topology
        letI : ChartedSpace H Y.M := Y.charted
        letI : IsManifold I ∞ Y.M := Y.smooth
        letI : T2Space Y.M := Y.t2
        letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
        letI : MetricSpace Y.M := (P (Lphi.φ k)).ms
        (∀ alpha : LiveSlot L inp.pack r,
          U alpha ⊆ Metric.ball 0
              (inp.normalBounds.radius (Lphi.φ k)
                (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))) ∧
          U alpha ⊆ Metric.ball 0
              (expMapC2Radius (I := I) Y.metric
                (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))) ∧
          Set.MapsTo
            (fun z => expMapDiffeo (I := I) Y.metric
              (seqCenterD inp.decay P Lphi k (alpha.1 : Nat)) z)
            (U alpha)
            (Lphi.hatBall inp.decay inp.D P inp.pack r k alpha.1 ∩
              ⋃ gamma : Fin (inp.pack.A r),
                Lphi.innerBall inp.decay inp.D P inp.pack r k gamma)) ∧
        Lphi.hatSourceBall inp.decay P r k ⊆
          ⋃ alpha : LiveSlot L inp.pack r,
            (fun z => expMapDiffeo (I := I) Y.metric
              (seqCenterD inp.decay P Lphi k (alpha.1 : Nat)) z) '' U alpha) ∧
      (∀ alpha,
        HasAtomWeightLim (I := I) inp.decay inp.hD P Lphi inp.realizes
          inp.pack r hr
          (fun k => seqCenterD inp.decay P Lphi k (alpha.1 : Nat))
          (U alpha) (aInf alpha)) ∧
      (∀ alpha target,
        ContDiffOn Real (⊤ : ℕ∞) (Jinf alpha target)
            (Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat))) ∧
        ContDiffOn Real (⊤ : ℕ∞) (Jbarinf alpha target)
            (Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat))) ∧
        ContinuousOn (Jinf alpha target)
            (Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat))) ∧
        ContinuousOn (Jbarinf alpha target)
            (Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat))) ∧
        MapCInfConvOnCompacts
          (Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat)))
          (fun k => normalTransition (I := I) (X.obj (Lphi.φ k))
            (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))
            (seqCenterD inp.decay P Lphi k (target.1.1 : Nat)))
          (Jinf alpha target) ∧
        MapCInfConvOnCompacts
          (Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat)))
          (fun k => normalTransition (I := I) (X.obj (Lphi.φ k))
            (seqCenterD inp.decay P Lphi k (target.1.1 : Nat))
            (seqCenterD inp.decay P Lphi k (alpha.1 : Nat)))
          (Jbarinf alpha target) ∧
        (∀ z, z ∈ Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat)) →
          Jinf alpha target z ∈
              Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat)) →
            Jbarinf alpha target (Jinf alpha target z) = z) ∧
        (∀ w, w ∈ Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat)) →
          Jbarinf alpha target w ∈
              Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat)) →
            Jinf alpha target (Jbarinf alpha target w) = w)) ∧
      (∀ (alpha : LiveSlot L inp.pack r)
          (target : InterSlot L inp.pack r alpha) (k : Nat),
        ContDiffOn Real (⊤ : ℕ∞)
          (normalTransition (I := I) (X.obj (Lphi.φ k))
            (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))
            (seqCenterD inp.decay P Lphi k (target.1.1 : Nat)))
          (Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat))) ∧
        ContDiffOn Real (⊤ : ℕ∞)
          (normalTransition (I := I) (X.obj (Lphi.φ k))
            (seqCenterD inp.decay P Lphi k (target.1.1 : Nat))
            (seqCenterD inp.decay P Lphi k (alpha.1 : Nat)))
          (Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat)))) ∧
      ∀ alpha z, z ∈ U alpha → ∀ gamma : Fin (inp.pack.A r),
        rawWeights
          (cutRaw
            (aInf alpha (baseIndex inp.decay inp.realizes inp.pack hr))
            (aInf alpha) (baseIndex inp.decay inp.realizes inp.pack hr))
          z gamma ≠ 0 →
        ∃ target : InterSlot L inp.pack r alpha,
          target.1.1 = gamma ∧
            Jinf alpha target z ∈
              Metric.closedBall 0 (6 * L.lamInf (gamma : Nat)) := by
  classical
  let PairSlot := Σ alpha : LiveSlot L inp.pack r,
    InterSlot L inp.pack r alpha
  letI (alpha : LiveSlot L inp.pack r) : Finite (InterSlot L inp.pack r alpha) :=
    Finite.of_injective
      (fun target : InterSlot L inp.pack r alpha => target.1.1)
      (by
        intro a b hab
        apply Subtype.ext
        apply Subtype.ext
        exact hab)
  letI : Finite PairSlot := inferInstance
  obtain ⟨psi, hpsi, gInf, U, C0, C1, hginf, hg, hUopen, hU8,
      hC0, hC1, hC01, hC1U, hC0convex, hC0zero, eta, heta, hcore⟩ :=
    inp.exists_live_cores h8 hradD hradRatio P L r
  have hcover : ∀ᶠ k in Filter.atTop,
      let Y := X.obj (L.φ (psi k))
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space Y.M := Y.t2
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      letI : MetricSpace Y.M := (P (L.φ (psi k))).ms
      (∀ alpha : LiveSlot L inp.pack r,
        U alpha ⊆ Metric.ball 0
            (inp.normalBounds.radius (L.φ (psi k))
              (seqCenterD inp.decay P L (psi k) (alpha.1 : Nat))) ∧
        U alpha ⊆ Metric.ball 0
            (expMapC2Radius (I := I) Y.metric
              (seqCenterD inp.decay P L (psi k) (alpha.1 : Nat))) ∧
        Set.MapsTo
          (fun z => expMapDiffeo (I := I) Y.metric
            (seqCenterD inp.decay P L (psi k) (alpha.1 : Nat)) z)
          (U alpha)
          (L.hatBall inp.decay inp.D P inp.pack r (psi k) alpha.1 ∩
            ⋃ gamma : Fin (inp.pack.A r),
              L.innerBall inp.decay inp.D P inp.pack r (psi k) gamma)) ∧
      L.hatSourceBall inp.decay P r (psi k) ⊆
        ⋃ alpha : LiveSlot L inp.pack r,
          (fun z => expMapDiffeo (I := I) Y.metric
            (seqCenterD inp.decay P L (psi k) (alpha.1 : Nat)) z) '' U alpha := by
    filter_upwards [hcore] with k hk
    refine ⟨hk.1, ?_⟩
    intro y hy
    obtain ⟨alpha, v, hv, rfl⟩ := mem_iUnion.mp (hk.2.1 hy)
    refine mem_iUnion.mpr ⟨alpha, v, ?_, rfl⟩
    exact hC1U alpha (interior_subset (hC01 alpha (interior_subset hv)))
  let L0 := L.subseq hpsi
  let live0 : LiveSlot L inp.pack r → LiveSlot L0 inp.pack r := fun alpha =>
    ⟨alpha.1, by simpa only [L0, NetLimitData.subseq] using alpha.2⟩
  have hinter0 (pair : PairSlot) : ∀ᶠ k in Filter.atTop,
      BInter inp.decay inp.D P L0.lamInf
        ((live0 pair.1).1 : Nat) ((live0 pair.2.1).1 : Nat) (L0.φ k) := by
    simpa only [L0, live0, NetLimitData.subseq, NetLimitData.subseq_lamInf,
      Function.comp_apply] using
        hpsi.tendsto_atTop.eventually pair.2.2
  obtain ⟨tau, htau, J, Jbar, hspec⟩ :=
    inp.exists_pair_trans hradD hradRatio P L0 r
      (fun pair : PairSlot => live0 pair.1)
      (fun pair : PairSlot => live0 pair.2.1)
      hinter0
  have hpair : ∀ᶠ k in Filter.atTop, ∀ pair : PairSlot,
      let x := seqCenterD inp.decay P L0 k ((live0 pair.1).1 : Nat)
      let y := seqCenterD inp.decay P L0 k ((live0 pair.2.1).1 : Nat)
      let Y := X.obj (L0.φ k)
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space Y.M := Y.t2
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      letI : MetricSpace Y.M := (P (L0.φ k)).ms
      ContDiffOn Real (⊤ : ℕ∞)
          (normalTransition (I := I) Y x y)
          (Metric.ball 0 (8 * L0.lamInf ((live0 pair.1).1 : Nat))) ∧
        NormalOverlapOn (I := I) Y x y
          (Metric.ball 0 (8 * L0.lamInf ((live0 pair.1).1 : Nat))) :=
    Filter.eventually_all.mpr fun pair =>
      (inp.pair_overlap_tail hradD hradRatio P L0 r
        (live0 pair.1) (live0 pair.2.1) (hinter0 pair)).mono fun _ hk =>
          ⟨hk.2.2.2.2.1, hk.2.2.2.2.2.1⟩
  obtain ⟨hgp, _hrad⟩ := inp.item3ScaleTails h8 hradD hradRatio P L r
  have hgp0 : Item3GpScaleTail (I := I)
      inp.decay inp.D P L0 inp.pack r :=
    hgp.subseq inp.decay inp.D P L inp.pack r hpsi
  have hall : ∀ᶠ k in Filter.atTop,
      (let Y := X.obj (L.φ (psi (tau k)))
       letI : TopologicalSpace Y.M := Y.topology
       letI : ChartedSpace H Y.M := Y.charted
       letI : IsManifold I ∞ Y.M := Y.smooth
       letI : T2Space Y.M := Y.t2
       letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
       letI : MetricSpace Y.M := (P (L.φ (psi (tau k)))).ms
       (∀ alpha : LiveSlot L inp.pack r,
          U alpha ⊆ Metric.ball 0
              (inp.normalBounds.radius (L.φ (psi (tau k)))
                (seqCenterD inp.decay P L (psi (tau k)) (alpha.1 : Nat))) ∧
          U alpha ⊆ Metric.ball 0
              (expMapC2Radius (I := I) Y.metric
                (seqCenterD inp.decay P L (psi (tau k)) (alpha.1 : Nat))) ∧
          Set.MapsTo
            (fun z => expMapDiffeo (I := I) Y.metric
              (seqCenterD inp.decay P L (psi (tau k)) (alpha.1 : Nat)) z)
            (U alpha)
            (L.hatBall inp.decay inp.D P inp.pack r (psi (tau k)) alpha.1 ∩
              ⋃ gamma : Fin (inp.pack.A r),
                L.innerBall inp.decay inp.D P inp.pack r (psi (tau k)) gamma)) ∧
        L.hatSourceBall inp.decay P r (psi (tau k)) ⊆
          ⋃ alpha : LiveSlot L inp.pack r,
            (fun z => expMapDiffeo (I := I) Y.metric
              (seqCenterD inp.decay P L (psi (tau k)) (alpha.1 : Nat)) z) '' U alpha) ∧
      Item3GpScaleAt (I := I) inp.decay inp.D P L0 inp.pack r (tau k) ∧
      (∀ pair : PairSlot,
        let x := seqCenterD inp.decay P L0 (tau k) ((live0 pair.1).1 : Nat)
        let y := seqCenterD inp.decay P L0 (tau k) ((live0 pair.2.1).1 : Nat)
        let Y := X.obj (L0.φ (tau k))
        letI : TopologicalSpace Y.M := Y.topology
        letI : ChartedSpace H Y.M := Y.charted
        letI : IsManifold I ∞ Y.M := Y.smooth
        letI : T2Space Y.M := Y.t2
        letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
        letI : MetricSpace Y.M := (P (L0.φ (tau k))).ms
        ContDiffOn Real (⊤ : ℕ∞)
            (normalTransition (I := I) Y x y)
            (Metric.ball 0 (8 * L0.lamInf ((live0 pair.1).1 : Nat))) ∧
          NormalOverlapOn (I := I) Y x y
            (Metric.ball 0 (8 * L0.lamInf ((live0 pair.1).1 : Nat)))) ∧
      (let Y := X.obj (L.φ (psi (tau k)))
       letI : TopologicalSpace Y.M := Y.topology
       letI : ChartedSpace H Y.M := Y.charted
       letI : IsManifold I ∞ Y.M := Y.smooth
       letI : T2Space Y.M := Y.t2
       letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
       letI : MetricSpace Y.M := (P (L.φ (psi (tau k)))).ms
       (L.hatSourceBall inp.decay P r (psi (tau k)) ⊆
         ⋃ alpha : LiveSlot L inp.pack r,
           (fun z => expMapDiffeo (I := I) Y.metric
             (seqCenterD inp.decay P L (psi (tau k)) (alpha.1 : Nat)) z) ''
              interior (C0 alpha)) ∧
       ∀ y ∈ L.hatSourceBall inp.decay P r (psi (tau k)),
         ∃ (alpha : LiveSlot L inp.pack r) (z : E),
           expMapDiffeo (I := I) Y.metric
               (seqCenterD inp.decay P L (psi (tau k)) (alpha.1 : Nat)) z = y ∧
             Metric.closedBall z (eta alpha) ⊆ interior (C0 alpha)) := by
    filter_upwards [htau.tendsto_atTop.eventually hcover,
      htau.tendsto_atTop.eventually hcore,
      htau.tendsto_atTop.eventually hgp0,
      htau.tendsto_atTop.eventually hpair]
      with k hcoverK hcoreK hgpK hpairK
    exact ⟨hcoverK, hgpK, hpairK, hcoreK.2⟩
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hall
  let shift : Nat → Nat := fun k => k + N
  have hshift : StrictMono shift := by
    simpa only [shift] using strictMono_id.add_const N
  let phi : Nat → Nat := psi ∘ tau ∘ shift
  have hphi : StrictMono phi := hpsi.comp (htau.comp hshift)
  let Lphi := L.subseq hphi
  let Jinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E :=
    fun alpha target => J ⟨alpha, target⟩
  let Jbarinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E :=
    fun alpha target => Jbar ⟨alpha, target⟩
  let aInf : (alpha : LiveSlot L inp.pack r) →
      Fin (inp.pack.A r) → E → Real := fun alpha gamma =>
    if htarget : ∃ target : InterSlot L inp.pack r alpha,
        target.1.1 = gamma then
      let target := Classical.choose htarget
      fun z => stepCBump (L.lamInf (gamma : Nat))
        (inp.decay.lambda_pos inp.hD (L.rInf (gamma : Nat)))
        (gInf z target.1 (Jinf alpha target z) (Jinf alpha target z))
    else fun _ => 0
  have hlimAll : ∀ alpha,
      HasAtomWeightLim (I := I) inp.decay inp.hD P Lphi inp.realizes
        inp.pack r hr
        (fun k => seqCenterD inp.decay P Lphi k (alpha.1 : Nat))
        (U alpha) (aInf alpha) := by
    intro alpha
    let beta : ∀ k : Nat, (X.obj (Lphi.φ k)).M := fun k =>
      seqCenterD inp.decay P Lphi k (alpha.1 : Nat)
    have hgpPhi (k : Nat) : Item3GpScaleAt (I := I)
        inp.decay inp.D P Lphi inp.pack r k := by
      have hk := hN (shift k) (by simpa only [shift] using Nat.le_add_left N k)
      simpa only [Item3GpScaleAt, Lphi, phi, L0, Function.comp_apply,
        NetLimitData.subseq, NetLimitData.subseq_lamInf] using hk.2.1
    have hUexpPhi (k : Nat) :
        letI : TopologicalSpace (X.obj (Lphi.φ k)).M := (X.obj (Lphi.φ k)).topology
        letI : ChartedSpace H (X.obj (Lphi.φ k)).M := (X.obj (Lphi.φ k)).charted
        letI : IsManifold I ∞ (X.obj (Lphi.φ k)).M := (X.obj (Lphi.φ k)).smooth
        letI : T2Space (TangentBundle I (X.obj (Lphi.φ k)).M) :=
          (X.obj (Lphi.φ k)).t2TangentBundle
        U alpha ⊆ Metric.ball 0
          (expMapC2Radius (I := I) (X.obj (Lphi.φ k)).metric (beta k)) := by
      have hk := hN (shift k) (by simpa only [shift] using Nat.le_add_left N k)
      simpa only [beta, Lphi, phi, Function.comp_apply, seqCenterD_subseq] using
        (hk.1.1 alpha).2.1
    have hsourcePhi (k : Nat) :
        letI : TopologicalSpace (X.obj (Lphi.φ k)).M := (X.obj (Lphi.φ k)).topology
        letI : ChartedSpace H (X.obj (Lphi.φ k)).M := (X.obj (Lphi.φ k)).charted
        letI : IsManifold I ∞ (X.obj (Lphi.φ k)).M := (X.obj (Lphi.φ k)).smooth
        letI : T2Space (TangentBundle I (X.obj (Lphi.φ k)).M) :=
          (X.obj (Lphi.φ k)).t2TangentBundle
        Set.MapsTo
          (fun z => expMapDiffeo (I := I) (X.obj (Lphi.φ k)).metric (beta k) z)
          (U alpha) (Lphi.hatBall inp.decay inp.D P inp.pack r k alpha.1) := by
      have hk := hN (shift k) (by simpa only [shift] using Nat.le_add_left N k)
      intro z hz
      have hmem := (hk.1.1 alpha).2.2 hz
      simpa only [beta, Lphi, phi, Function.comp_apply, seqCenterD_subseq,
        NetLimitData.hatBall_subseq] using hmem.1
    have hcoverPhi (k : Nat) :
        letI : TopologicalSpace (X.obj (Lphi.φ k)).M := (X.obj (Lphi.φ k)).topology
        letI : ChartedSpace H (X.obj (Lphi.φ k)).M := (X.obj (Lphi.φ k)).charted
        letI : IsManifold I ∞ (X.obj (Lphi.φ k)).M := (X.obj (Lphi.φ k)).smooth
        letI : T2Space (TangentBundle I (X.obj (Lphi.φ k)).M) :=
          (X.obj (Lphi.φ k)).t2TangentBundle
        Set.MapsTo
          (fun z => expMapDiffeo (I := I) (X.obj (Lphi.φ k)).metric (beta k) z)
          (U alpha)
          (⋃ gamma : Fin (inp.pack.A r),
            Lphi.innerBall inp.decay inp.D P inp.pack r k gamma) := by
      have hk := hN (shift k) (by simpa only [shift] using Nat.le_add_left N k)
      intro z hz
      have hmem := (hk.1.1 alpha).2.2 hz
      simpa only [beta, Lphi, phi, Function.comp_apply, seqCenterD_subseq,
        NetLimitData.innerBall_subseq] using hmem.2
    have hgPhi : MapCInfConvOnCompacts Set.univ
        (fun k _ gamma => normalCoordMetric (I := I) (X.obj (Lphi.φ k))
          (seqCenterD inp.decay P Lphi k (gamma.1 : Nat)) 0) gInf := by
      simpa only [Lphi, phi, Function.comp_apply, seqCenterD_subseq] using
        hg.comp_subseq (htau.comp hshift)
    have hgU : MapCInfConvOnCompacts (U alpha)
        (fun k _ gamma => normalCoordMetric (I := I) (X.obj (Lphi.φ k))
          (seqCenterD inp.decay P Lphi k (gamma.1 : Nat)) 0) gInf := by
      intro K hK hKU p
      exact hgPhi K hK (hKU.trans (Set.subset_univ (U alpha))) p
    have hginfU : ContDiffOn Real (∞ : WithTop ℕ∞) gInf (U alpha) :=
      hginf.mono (Set.subset_univ (U alpha))
    have hJInf (target : InterSlot L inp.pack r alpha) :
        ContDiffOn Real (∞ : WithTop ℕ∞) (Jinf alpha target) (U alpha) :=
      (hspec (⟨alpha, target⟩ : PairSlot)).1.mono (hU8 alpha)
    have hJConv (target : InterSlot L inp.pack r alpha) :
        MapCInfConvOnCompacts (U alpha)
          (fun k => normalTransition (I := I) (X.obj (Lphi.φ k))
            (beta k) (seqCenterD inp.decay P Lphi k (target.1.1 : Nat)))
          (Jinf alpha target) := by
      intro K hK hKU p
      have hconv :=
        (hspec (⟨alpha, target⟩ : PairSlot)).2.2.2.2.1.comp_subseq hshift
          K hK (hKU.trans (hU8 alpha)) p
      simpa only [Jinf, beta, Lphi, phi, L0, live0, NetLimitData.subseq,
        Function.comp_apply, seqCenterD_subseq, NetLimitData.subseq_lamInf] using hconv
    have hJStage (target : InterSlot L inp.pack r alpha) (k : Nat) :
        ContDiffOn Real (∞ : WithTop ℕ∞)
          (normalTransition (I := I) (X.obj (Lphi.φ k))
            (beta k) (seqCenterD inp.decay P Lphi k (target.1.1 : Nat)))
          (U alpha) := by
      have hk := hN (shift k) (by simpa only [shift] using Nat.le_add_left N k)
      have hsmooth := (hk.2.2.1 (⟨alpha, target⟩ : PairSlot)).1.mono (hU8 alpha)
      simpa only [beta, Lphi, phi, L0, live0, NetLimitData.subseq,
        Function.comp_apply, seqCenterD_subseq, NetLimitData.subseq_lamInf] using hsmooth
    have hOverlap (target : InterSlot L inp.pack r alpha) (k : Nat) :
        NormalOverlapOn (I := I) (X.obj (Lphi.φ k))
          (beta k) (seqCenterD inp.decay P Lphi k (target.1.1 : Nat))
          (U alpha) := by
      have hk := hN (shift k) (by simpa only [shift] using Nat.le_add_left N k)
      have hover := (hk.2.2.1 (⟨alpha, target⟩ : PairSlot)).2
      intro z hz
      have hz' := hover z (hU8 alpha hz)
      simpa only [beta, Lphi, phi, L0, live0, NetLimitData.subseq,
        Function.comp_apply, seqCenterD_subseq, NetLimitData.subseq_lamInf] using hz'
    have hatom (gamma : Fin (inp.pack.A r)) :
        MapCInfConvOnCompacts (U alpha)
          (fun k => seqAtomChart (I := I) inp.decay inp.hD P Lphi inp.pack r
            beta gamma k) (aInf alpha gamma) := by
      by_cases htarget : ∃ target : InterSlot L inp.pack r alpha,
          target.1.1 = gamma
      · let target := Classical.choose htarget
        have hslot : target.1.1 = gamma := Classical.choose_spec htarget
        have hgamma : Lphi.alive (gamma : Nat) = true := by
          simpa only [Lphi, NetLimitData.subseq, hslot] using target.1.2
        have hraw := quadPiBump_conv (hUopen alpha) hgU (hJConv target)
          (fun _ => contDiffOn_const) hginfU (hJStage target) (hJInf target)
          target.1 (stepCBump (L.lamInf (gamma : Nat))
            (inp.decay.lambda_pos inp.hD (L.rInf (gamma : Nat))))
          (stepCBump (L.lamInf (gamma : Nat))
            (inp.decay.lambda_pos inp.hD (L.rInf (gamma : Nat)))).contDiff
        have hstep : MapCInfConvOnCompacts (U alpha)
            (fun k => stepCAtomChart (I := I) (X.obj (Lphi.φ k)) (beta k)
              (seqCenterD inp.decay P Lphi k (gamma : Nat))
              (L.lamInf (gamma : Nat))
              (inp.decay.lambda_pos inp.hD (L.rInf (gamma : Nat))))
            (aInf alpha gamma) := by
          refine hraw.congr (hUopen alpha) (fun k z hz => ?_) (fun z _hz => ?_)
          · simpa only [stepCAtomChart, hslot] using
              (stepCAtom_readout (I := I) (X.obj (Lphi.φ k)) (beta k)
                (seqCenterD inp.decay P Lphi k (target.1.1 : Nat))
                (L.lamInf (gamma : Nat))
                (inp.decay.lambda_pos inp.hD (L.rInf (gamma : Nat)))
                ((hOverlap target k) z hz).2)
          · simp only [aInf, dif_pos htarget, target]
        exact seqAtom_live_conv (I := I) inp.decay inp.hD P Lphi inp.pack r
          beta gamma (hUopen alpha) hgamma (by
            simpa only [Lphi, NetLimitData.subseq_lamInf] using hstep)
      · cases hgamma : L.alive (gamma : Nat) with
        | false =>
            have hgammaPhi : Lphi.alive (gamma : Nat) = false := by
              simpa only [Lphi, NetLimitData.subseq] using hgamma
            simpa only [aInf, dif_neg htarget] using
              (seqAtom_dead_conv (I := I) inp.decay inp.hD P Lphi inp.pack r
                beta gamma (hUopen alpha) hgammaPhi)
        | true =>
            rcases hstable (alpha.1 : Nat) (gamma : Nat) with hinter | hdisjoint
            · exact (htarget
                ⟨⟨⟨gamma, hgamma⟩, hinter⟩, rfl⟩).elim
            · have hdisjointPhi : ∀ᶠ k in Filter.atTop,
                  ¬ BInter inp.decay inp.D P Lphi.lamInf
                    (alpha.1 : Nat) (gamma : Nat) (Lphi.φ k) := by
                simpa only [Lphi, NetLimitData.subseq, Function.comp_apply,
                  NetLimitData.subseq_lamInf] using
                    hphi.tendsto_atTop.eventually hdisjoint
              have hgpTail : Item3GpScaleTail (I := I)
                  inp.decay inp.D P Lphi inp.pack r :=
                Filter.Eventually.of_forall hgpPhi
              have hsourceTail : ∀ᶠ k in Filter.atTop,
                  letI : TopologicalSpace (X.obj (Lphi.φ k)).M :=
                    (X.obj (Lphi.φ k)).topology
                  letI : ChartedSpace H (X.obj (Lphi.φ k)).M :=
                    (X.obj (Lphi.φ k)).charted
                  letI : IsManifold I ∞ (X.obj (Lphi.φ k)).M :=
                    (X.obj (Lphi.φ k)).smooth
                  letI : T2Space (TangentBundle I (X.obj (Lphi.φ k)).M) :=
                    (X.obj (Lphi.φ k)).t2TangentBundle
                  Set.MapsTo
                    (fun z => expMapDiffeo (I := I) (X.obj (Lphi.φ k)).metric
                      (beta k) z)
                    (U alpha)
                    (Lphi.hatBall inp.decay inp.D P inp.pack r k alpha.1) :=
                Filter.Eventually.of_forall hsourcePhi
              simpa only [aInf, dif_neg htarget] using
                (atom_disjoint_conv (I := I) inp.decay inp.hD P Lphi inp.pack r
                  hgpTail beta alpha.1 gamma (hUopen alpha) hsourceTail
                  hdisjointPhi)
    have hdead (gamma : Fin (inp.pack.A r))
        (hgamma : Lphi.alive (gamma : Nat) = false) :
        aInf alpha gamma = 0 := by
      have hnone : ¬ ∃ target : InterSlot L inp.pack r alpha,
          target.1.1 = gamma := by
        rintro ⟨target, hslot⟩
        have htrue : Lphi.alive (gamma : Nat) = true := by
          simpa only [Lphi, NetLimitData.subseq, hslot] using target.1.2
        rw [hgamma] at htrue
        contradiction
      simp only [aInf, dif_neg hnone]
      rfl
    have hatomSmooth (k : Nat) (gamma : Fin (inp.pack.A r)) :
        ContDiffOn Real (∞ : WithTop ℕ∞)
          (seqAtomChart (I := I) inp.decay inp.hD P Lphi inp.pack r
            beta gamma k) (U alpha) :=
      seqAtomChart_smooth (I := I) inp.decay inp.hD P Lphi inp.pack r k
        (hgpPhi k) beta gamma (hUexpPhi k)
    have hatomInfSmooth (gamma : Fin (inp.pack.A r)) :
        ContDiffOn Real (∞ : WithTop ℕ∞) (aInf alpha gamma) (U alpha) := by
      by_cases htarget : ∃ target : InterSlot L inp.pack r alpha,
          target.1.1 = gamma
      · let target := Classical.choose htarget
        have hquad : ContDiffOn Real (∞ : WithTop ℕ∞)
            (fun z => gInf z target.1 (Jinf alpha target z)
              (Jinf alpha target z)) (U alpha) :=
          ((contDiffOn_pi.mp hginfU target.1).clm_apply (hJInf target)).clm_apply
            (hJInf target)
        simpa only [aInf, dif_pos htarget, target] using
          (stepCBump (L.lamInf (gamma : Nat))
            (inp.decay.lambda_pos inp.hD (L.rInf (gamma : Nat)))).contDiff.comp_contDiffOn
              hquad
      · simpa only [aInf, dif_neg htarget] using
          (contDiffOn_const : ContDiffOn Real (∞ : WithTop ℕ∞)
            (fun _ : E => (0 : Real)) (U alpha))
    exact HasAtomWeightLim.of_atoms (I := I) inp.hD P Lphi inp.realizes inp.pack
      r hr hgpPhi beta (U alpha) (hUopen alpha) hcoverPhi (aInf alpha)
      hdead hatom hatomSmooth hatomInfSmooth
  refine ⟨phi, hphi, U, C0, C1, aInf, Jinf, Jbarinf, ?_⟩
  dsimp only
  refine ⟨hUopen, hU8, hC0, hC1, hC01, hC1U, hC0convex, hC0zero,
    ?_, ?_, ?_, hlimAll, ?_, ?_, ?_⟩
  · refine ⟨eta, heta, ?_⟩
    intro k
    have hk := hN (shift k) (by simpa only [shift] using Nat.le_add_left N k)
    simpa only [Lphi, phi, Function.comp_apply,
      seqCenterD_subseq, NetLimitData.hatSourceBall_subseq] using hk.2.2.2.2
  · intro k
    have hk := hN (shift k) (by simpa only [shift] using Nat.le_add_left N k)
    simpa only [Lphi, phi, Function.comp_apply,
      seqCenterD_subseq, NetLimitData.hatSourceBall_subseq] using hk.2.2.2.1
  · intro k
    have hk := hN (shift k) (by simpa only [shift] using Nat.le_add_left N k)
    simpa only [Lphi, phi, Function.comp_apply,
      seqCenterD_subseq, NetLimitData.hatBall_subseq,
      NetLimitData.innerBall_subseq, NetLimitData.hatSourceBall_subseq] using hk.1
  · intro alpha target
    have hs := hspec (⟨alpha, target⟩ : PairSlot)
    refine ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, ?_, ?_,
      hs.2.2.2.2.2.2.1, hs.2.2.2.2.2.2.2⟩
    · simpa only [Jinf, Lphi, phi, L0, live0, NetLimitData.subseq,
        Function.comp_apply, seqCenterD_subseq, NetLimitData.subseq_lamInf] using
        hs.2.2.2.2.1.comp_subseq hshift
    · simpa only [Jbarinf, Lphi, phi, L0, live0, NetLimitData.subseq,
        Function.comp_apply, seqCenterD_subseq, NetLimitData.subseq_lamInf] using
        hs.2.2.2.2.2.1.comp_subseq hshift
  · intro alpha target k
    let revTarget : InterSlot L inp.pack r target.1 :=
      ⟨alpha, target.2.mono fun _ hk =>
        BInter.symm inp.decay inp.D P L.lamInf hk⟩
    have hk := hN (shift k) (by
      simpa only [shift] using Nat.le_add_left N k)
    have hf := (hk.2.2.1 (⟨alpha, target⟩ : PairSlot)).1
    have hr := (hk.2.2.1 (⟨target.1, revTarget⟩ : PairSlot)).1
    constructor
    · simpa only [Lphi, phi, L0, live0, NetLimitData.subseq,
        Function.comp_apply, seqCenterD_subseq,
        NetLimitData.subseq_lamInf] using hf
    · simpa only [revTarget, Lphi, phi, L0, live0, NetLimitData.subseq,
        Function.comp_apply, seqCenterD_subseq,
        NetLimitData.subseq_lamInf] using hr
  · intro alpha z hz gamma hweight
    have hnum : aInf alpha gamma z ≠ 0 :=
      num_ne_of_cut_ne (num_ne_of_raw_ne hweight)
    have htarget : ∃ target : InterSlot L inp.pack r alpha,
        target.1.1 = gamma := by
      by_contra hnone
      apply hnum
      simp only [aInf, dif_neg hnone]
    let target := Classical.choose htarget
    have hslot : target.1.1 = gamma := Classical.choose_spec htarget
    let alphaPhi : LiveSlot Lphi inp.pack r :=
      ⟨alpha.1, by simpa only [Lphi, NetLimitData.subseq] using alpha.2⟩
    let gammaPhi : LiveSlot Lphi inp.pack r :=
      ⟨target.1.1, by simpa only [Lphi, NetLimitData.subseq] using target.1.2⟩
    have hgpPhi : Item3GpScaleTail (I := I)
        inp.decay inp.D P Lphi inp.pack r :=
      Filter.Eventually.of_forall fun k => by
        have hk := hN (shift k) (by simpa only [shift] using Nat.le_add_left N k)
        simpa only [Item3GpScaleAt, Lphi, phi, L0, Function.comp_apply,
          NetLimitData.subseq, NetLimitData.subseq_lamInf] using hk.2.1
    have hlimPhi : HasAtomWeightLim (I := I) inp.decay inp.hD P Lphi
        inp.realizes inp.pack r hr
        (fun k => seqCenterD inp.decay P Lphi k (alphaPhi.1 : Nat))
        (U alpha) (aInf alpha) := by
      simpa only [alphaPhi] using hlimAll alpha
    have hB : MapCInfConvOnCompacts (U alpha)
        (fun k => normalTransition (I := I) (X.obj (Lphi.φ k))
          (seqCenterD inp.decay P Lphi k (alphaPhi.1 : Nat))
          (seqCenterD inp.decay P Lphi k (gammaPhi.1 : Nat)))
        (Jinf alpha target) := by
      intro K hK hKU p
      have hconv :=
        (hspec (⟨alpha, target⟩ : PairSlot)).2.2.2.2.1.comp_subseq hshift
          K hK (hKU.trans (hU8 alpha)) p
      simpa only [Jinf, alphaPhi, gammaPhi, Lphi, phi, L0, live0,
        NetLimitData.subseq, Function.comp_apply, seqCenterD_subseq,
        NetLimitData.subseq_lamInf] using hconv
    refine ⟨target, hslot, ?_⟩
    have hmem := hlimPhi.binf_of_live inp hradD hradRatio P Lphi r hr
      hgpPhi alphaPhi (U alpha) (aInf alpha) (fun k : Nat => k)
      strictMono_id gammaPhi (Jinf alpha target) (by
        simpa only [Function.id_def] using hB) hz (by
          simpa only [gammaPhi, hslot] using hweight)
    simpa only [Jinf, gammaPhi, hslot, Lphi, NetLimitData.subseq_lamInf] using hmem



def HasCompactCover {Y J : Type*} [TopologicalSpace Y]
    (sourceBall : Set Y) (sourcePatch : J → Set Y) : Prop :=
  ∃ K : J → Set Y, (∀ j, IsCompact (K j)) ∧
    (∀ j, K j ⊆ sourcePatch j) ∧ sourceBall = ⋃ j, K j






def HasSuppConvData
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P)
    (r : Real) (hr : 0 ≤ r)
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (U : LiveSlot L inp.pack r → Set E)
    (C0 C1 : LiveSlot L inp.pack r → Set E)
    (aInf : (alpha : LiveSlot L inp.pack r) →
      Fin (inp.pack.A r) → E → Real)
    (Jinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (Jbarinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E) : Prop :=
  let Lphi := L.subseq hphi
  (∀ alpha, IsOpen (U alpha)) ∧
  (∀ alpha, U alpha ⊆
    Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat))) ∧
  (∀ alpha, IsCompact (C0 alpha)) ∧
  (∀ alpha, IsCompact (C1 alpha)) ∧
  (∀ alpha, C0 alpha ⊆ interior (C1 alpha)) ∧
  (∀ alpha, C1 alpha ⊆ U alpha) ∧
  (∀ alpha, Convex Real (C0 alpha)) ∧
  (∀ alpha, (0 : E) ∈ C0 alpha) ∧
  (∃ eta : LiveSlot L inp.pack r → Real,
    (∀ alpha, 0 < eta alpha) ∧
    ∀ k,
      let Y := X.obj (Lphi.φ k)
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space Y.M := Y.t2
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      letI : MetricSpace Y.M := (P (Lphi.φ k)).ms
      ∀ y ∈ Lphi.hatSourceBall inp.decay P r k,
        ∃ (alpha : LiveSlot L inp.pack r) (z : E),
          expMapDiffeo (I := I) Y.metric
              (seqCenterD inp.decay P Lphi k (alpha.1 : Nat)) z = y ∧
            Metric.closedBall z (eta alpha) ⊆ interior (C0 alpha)) ∧
  (∀ k,
    let Y := X.obj (Lphi.φ k)
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space Y.M := Y.t2
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    letI : MetricSpace Y.M := (P (Lphi.φ k)).ms
    Lphi.hatSourceBall inp.decay P r k ⊆
      ⋃ alpha : LiveSlot L inp.pack r,
        (fun z => expMapDiffeo (I := I) Y.metric
          (seqCenterD inp.decay P Lphi k (alpha.1 : Nat)) z) ''
            interior (C0 alpha)) ∧
  (∀ k,
    let Y := X.obj (Lphi.φ k)
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space Y.M := Y.t2
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    letI : MetricSpace Y.M := (P (Lphi.φ k)).ms
    (∀ alpha : LiveSlot L inp.pack r,
      U alpha ⊆ Metric.ball 0
          (inp.normalBounds.radius (Lphi.φ k)
            (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))) ∧
      U alpha ⊆ Metric.ball 0
          (expMapC2Radius (I := I) Y.metric
            (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))) ∧
      Set.MapsTo
        (fun z => expMapDiffeo (I := I) Y.metric
          (seqCenterD inp.decay P Lphi k (alpha.1 : Nat)) z)
        (U alpha)
        (Lphi.hatBall inp.decay inp.D P inp.pack r k alpha.1 ∩
          ⋃ gamma : Fin (inp.pack.A r),
            Lphi.innerBall inp.decay inp.D P inp.pack r k gamma)) ∧
    Lphi.hatSourceBall inp.decay P r k ⊆
      ⋃ alpha : LiveSlot L inp.pack r,
        (fun z => expMapDiffeo (I := I) Y.metric
          (seqCenterD inp.decay P Lphi k (alpha.1 : Nat)) z) '' U alpha) ∧
  (∀ alpha,
    HasAtomWeightLim (I := I) inp.decay inp.hD P Lphi inp.realizes
      inp.pack r hr
      (fun k => seqCenterD inp.decay P Lphi k (alpha.1 : Nat))
      (U alpha) (aInf alpha)) ∧
  (∀ alpha,
    centerAverage.WeightDataOn (U alpha)
      (fun _ : Fin (inp.pack.A r) => Set.univ)
      (fun z gamma =>
        rawWeights
          (cutRaw
            (aInf alpha (baseIndex inp.decay inp.realizes inp.pack hr))
            (aInf alpha) (baseIndex inp.decay inp.realizes inp.pack hr))
          z gamma)) ∧
  (∀ alpha target,
    ContDiffOn Real (⊤ : ℕ∞) (Jinf alpha target)
        (Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat))) ∧
    ContDiffOn Real (⊤ : ℕ∞) (Jbarinf alpha target)
        (Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat))) ∧
    ContinuousOn (Jinf alpha target)
        (Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat))) ∧
    ContinuousOn (Jbarinf alpha target)
        (Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat))) ∧
    MapCInfConvOnCompacts
      (Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat)))
      (fun k => normalTransition (I := I) (X.obj (Lphi.φ k))
        (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))
        (seqCenterD inp.decay P Lphi k (target.1.1 : Nat)))
      (Jinf alpha target) ∧
    MapCInfConvOnCompacts
      (Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat)))
      (fun k => normalTransition (I := I) (X.obj (Lphi.φ k))
        (seqCenterD inp.decay P Lphi k (target.1.1 : Nat))
        (seqCenterD inp.decay P Lphi k (alpha.1 : Nat)))
      (Jbarinf alpha target) ∧
    (∀ z, z ∈ Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat)) →
      Jinf alpha target z ∈
          Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat)) →
        Jbarinf alpha target (Jinf alpha target z) = z) ∧
    ∀ w, w ∈ Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat)) →
      Jbarinf alpha target w ∈
          Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat)) →
        Jinf alpha target (Jbarinf alpha target w) = w) ∧
  ∀ (alpha : LiveSlot L inp.pack r)
      (target : InterSlot L inp.pack r alpha) (k : Nat),
    ContDiffOn Real (⊤ : ℕ∞)
      (normalTransition (I := I) (X.obj (Lphi.φ k))
        (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))
        (seqCenterD inp.decay P Lphi k (target.1.1 : Nat)))
      (Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat))) ∧
    ContDiffOn Real (⊤ : ℕ∞)
      (normalTransition (I := I) (X.obj (Lphi.φ k))
        (seqCenterD inp.decay P Lphi k (target.1.1 : Nat))
        (seqCenterD inp.decay P Lphi k (alpha.1 : Nat)))
      (Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat)))



theorem HasSuppConvData.weight_on
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P)
    (r : Real) (hr : 0 ≤ r)
    {phi : Nat → Nat} {hphi : StrictMono phi}
    (U : LiveSlot L inp.pack r → Set E)
    (C0 C1 : LiveSlot L inp.pack r → Set E)
    (aInf : (alpha : LiveSlot L inp.pack r) →
      Fin (inp.pack.A r) → E → Real)
    (Jinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (Jbarinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (h : HasSuppConvData (I := I) inp P L r hr phi hphi U C0 C1
      aInf Jinf Jbarinf)
    (alpha : LiveSlot L inp.pack r) :
    let i0 := baseIndex inp.decay inp.realizes inp.pack hr
    let weightInf : E → Fin (inp.pack.A r) → Real := fun z gamma =>
      rawWeights (cutRaw (aInf alpha i0) (aInf alpha) i0) z gamma
    ContDiffOn Real (∞ : WithTop ℕ∞) weightInf (U alpha) ∧
      centerAverage.WeightDataOn (U alpha)
        (fun _ : Fin (inp.pack.A r) => Set.univ) weightInf := by
  dsimp only
  dsimp only [HasSuppConvData] at h
  rcases h with
    ⟨_hU, _hU8, _hC0, _hC1, _hC01, _hC1U, _hconvex, _hzero,
      _hbuffer, _hcore, _hcover,
      hlim, hweight, _htrans, _hsmooth⟩
  have hlim0 := hlim alpha
  dsimp only [HasAtomWeightLim] at hlim0
  rcases hlim0 with
    ⟨_hdead, _hatomC, _hatomInfC, _hatomConv, _hweightC,
      hweightInfC, _hweightConv⟩
  exact ⟨hweightInfC, hweight alpha⟩



theorem HasSuppConvData.core_on
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P)
    (r : Real) (hr : 0 ≤ r)
    {phi : Nat → Nat} {hphi : StrictMono phi}
    (U : LiveSlot L inp.pack r → Set E)
    (C0 C1 : LiveSlot L inp.pack r → Set E)
    (aInf : (alpha : LiveSlot L inp.pack r) →
      Fin (inp.pack.A r) → E → Real)
    (Jinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (Jbarinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (h : HasSuppConvData (I := I) inp P L r hr phi hphi U C0 C1
      aInf Jinf Jbarinf)
    (alpha : LiveSlot L inp.pack r) :
    IsOpen (U alpha) ∧ IsCompact (C0 alpha) ∧ IsCompact (C1 alpha) ∧
      C0 alpha ⊆ interior (C1 alpha) ∧ C1 alpha ⊆ U alpha := by
  dsimp only [HasSuppConvData] at h
  rcases h with
    ⟨hU, _hU8, hC0, hC1, hC01, hC1U, _hconvex, _hzero,
      _hbuffer, _hcore, _hcover,
      _hlim, _hweight, _htrans, _hsmooth⟩
  exact ⟨hU alpha, hC0 alpha, hC1 alpha, hC01 alpha, hC1U alpha⟩



theorem HasSuppConvData.core_shape
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P)
    (r : Real) (hr : 0 ≤ r)
    {phi : Nat → Nat} {hphi : StrictMono phi}
    (U : LiveSlot L inp.pack r → Set E)
    (C0 C1 : LiveSlot L inp.pack r → Set E)
    (aInf : (alpha : LiveSlot L inp.pack r) →
      Fin (inp.pack.A r) → E → Real)
    (Jinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (Jbarinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (h : HasSuppConvData (I := I) inp P L r hr phi hphi U C0 C1
      aInf Jinf Jbarinf)
    (alpha : LiveSlot L inp.pack r) :
    Convex Real (C0 alpha) ∧ (0 : E) ∈ C0 alpha := by
  dsimp only [HasSuppConvData] at h
  rcases h with
    ⟨_hU, _hU8, _hC0, _hC1, _hC01, _hC1U, hconvex, hzero,
      _hbuffer, _hcore, _hcover, _hlim, _hweight, _htrans, _hsmooth⟩
  exact ⟨hconvex alpha, hzero alpha⟩



theorem HasSuppConvData.buffer_cover
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P)
    (r : Real) (hr : 0 ≤ r)
    {phi : Nat → Nat} {hphi : StrictMono phi}
    (U : LiveSlot L inp.pack r → Set E)
    (C0 C1 : LiveSlot L inp.pack r → Set E)
    (aInf : (alpha : LiveSlot L inp.pack r) →
      Fin (inp.pack.A r) → E → Real)
    (Jinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (Jbarinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (h : HasSuppConvData (I := I) inp P L r hr phi hphi U C0 C1
      aInf Jinf Jbarinf) :
    let Lphi := L.subseq hphi
    ∃ eta : LiveSlot L inp.pack r → Real,
      (∀ alpha, 0 < eta alpha) ∧
      ∀ k,
        let Y := X.obj (Lphi.φ k)
        letI : TopologicalSpace Y.M := Y.topology
        letI : ChartedSpace H Y.M := Y.charted
        letI : IsManifold I ∞ Y.M := Y.smooth
        letI : T2Space Y.M := Y.t2
        letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
        letI : MetricSpace Y.M := (P (Lphi.φ k)).ms
        ∀ y ∈ Lphi.hatSourceBall inp.decay P r k,
          ∃ (alpha : LiveSlot L inp.pack r) (z : E),
            expMapDiffeo (I := I) Y.metric
                (seqCenterD inp.decay P Lphi k (alpha.1 : Nat)) z = y ∧
              Metric.closedBall z (eta alpha) ⊆ interior (C0 alpha) := by
  dsimp only [HasSuppConvData] at h
  rcases h with
    ⟨_hU, _hU8, _hC0, _hC1, _hC01, _hC1U, _hconvex, _hzero,
      hbuffer, _hcore, _hcover, _hlim, _hweight, _htrans, _hsmooth⟩
  exact hbuffer



theorem HasSuppConvData.source_cover
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P)
    (r : Real) (hr : 0 ≤ r)
    {phi : Nat → Nat} {hphi : StrictMono phi}
    (U : LiveSlot L inp.pack r → Set E)
    (C0 C1 : LiveSlot L inp.pack r → Set E)
    (aInf : (alpha : LiveSlot L inp.pack r) →
      Fin (inp.pack.A r) → E → Real)
    (Jinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (Jbarinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (h : HasSuppConvData (I := I) inp P L r hr phi hphi U C0 C1
      aInf Jinf Jbarinf)
    (k : Nat) :
    let Lphi := L.subseq hphi
    let Y := X.obj (Lphi.φ k)
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space Y.M := Y.t2
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    letI : MetricSpace Y.M := (P (Lphi.φ k)).ms
    Lphi.hatSourceBall inp.decay P r k ⊆
      ⋃ alpha : LiveSlot L inp.pack r,
        (fun z => expMapDiffeo (I := I) Y.metric
          (seqCenterD inp.decay P Lphi k (alpha.1 : Nat)) z) ''
            interior (C0 alpha) := by
  dsimp only [HasSuppConvData] at h
  rcases h with
    ⟨_hU, _hU8, _hC0, _hC1, _hC01, _hC1U, _hconvex, _hzero,
      _hbuffer, hcore, _hcover,
      _hlim, _hweight, _htrans, _hsmooth⟩
  exact hcore k



theorem HasSuppConvData.geom_on
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P)
    (r : Real) (hr : 0 ≤ r)
    {phi : Nat → Nat} {hphi : StrictMono phi}
    (U : LiveSlot L inp.pack r → Set E)
    (C0 C1 : LiveSlot L inp.pack r → Set E)
    (aInf : (alpha : LiveSlot L inp.pack r) →
      Fin (inp.pack.A r) → E → Real)
    (Jinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (Jbarinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (h : HasSuppConvData (I := I) inp P L r hr phi hphi U C0 C1
      aInf Jinf Jbarinf)
    (k : Nat) (alpha : LiveSlot L inp.pack r) :
    let Lphi := L.subseq hphi
    let Y := X.obj (Lphi.φ k)
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space Y.M := Y.t2
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    letI : MetricSpace Y.M := (P (Lphi.φ k)).ms
    U alpha ⊆ Metric.ball 0
        (inp.normalBounds.radius (Lphi.φ k)
          (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))) ∧
      U alpha ⊆ Metric.ball 0
        (expMapC2Radius (I := I) Y.metric
          (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))) ∧
      Set.MapsTo
        (fun z => expMapDiffeo (I := I) Y.metric
          (seqCenterD inp.decay P Lphi k (alpha.1 : Nat)) z)
        (U alpha)
        (Lphi.hatBall inp.decay inp.D P inp.pack r k alpha.1 ∩
          ⋃ gamma : Fin (inp.pack.A r),
            Lphi.innerBall inp.decay inp.D P inp.pack r k gamma) := by
  dsimp only [HasSuppConvData] at h
  rcases h with
    ⟨_hU, _hU8, _hC0, _hC1, _hC01, _hC1U, _hconvex, _hzero,
      _hbuffer, _hcore, hgeom,
      _hlim, _hweight, _htrans, _hsmooth⟩
  exact (hgeom k).1 alpha



theorem HasSuppConvData.subseq
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P)
    (r : Real) (hr : 0 ≤ r)
    {phi : Nat → Nat} (hphi : StrictMono phi)
    (U : LiveSlot L inp.pack r → Set E)
    (C0 C1 : LiveSlot L inp.pack r → Set E)
    (aInf : (alpha : LiveSlot L inp.pack r) →
      Fin (inp.pack.A r) → E → Real)
    (Jinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (Jbarinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (h : HasSuppConvData (I := I) inp P L r hr phi hphi U C0 C1
      aInf Jinf Jbarinf)
    {ψ : Nat → Nat} (hψ : StrictMono ψ) :
    HasSuppConvData (I := I) inp P L r hr (phi ∘ ψ) (hphi.comp hψ)
      U C0 C1 aInf Jinf Jbarinf := by
  dsimp only [HasSuppConvData] at h ⊢
  rcases h with
    ⟨hU, hU8, hC0, hC1, hC01, hC1U, hconvex, hzero,
      hbuffer, hcore, hcover, hweight,
      hweightData, htrans, hsmooth⟩
  refine ⟨hU, hU8, hC0, hC1, hC01, hC1U, hconvex, hzero, ?_, ?_, ?_, ?_,
    hweightData, ?_, ?_⟩
  · rcases hbuffer with ⟨eta, heta, hbuf⟩
    refine ⟨eta, heta, ?_⟩
    intro k
    simpa only [NetLimitData.subseq_phi, Function.comp_apply, seqCenterD_subseq,
      NetLimitData.hatSourceBall_subseq] using hbuf (ψ k)
  · intro k
    simpa only [NetLimitData.subseq_phi, Function.comp_apply, seqCenterD_subseq,
      NetLimitData.hatSourceBall_subseq] using hcore (ψ k)
  · intro k
    simpa only [NetLimitData.subseq_phi, Function.comp_apply, seqCenterD_subseq,
      NetLimitData.hatBall_subseq, NetLimitData.innerBall_subseq,
      NetLimitData.hatSourceBall_subseq] using hcover (ψ k)
  · intro alpha
    have hsub := (hweight alpha).subseq hψ
    simpa only [NetLimitData.subseq_phi, Function.comp_apply,
      seqCenterD_subseq] using hsub
  · intro alpha target
    rcases htrans alpha target with
      ⟨hJ, hJbar, hJcont, hJbarcont, hJconv, hJbarconv, hleft, hright⟩
    refine ⟨hJ, hJbar, hJcont, hJbarcont, ?_, ?_, hleft, hright⟩
    · have hsub := hJconv.comp_tendsto_atTop hψ.tendsto_atTop
      simpa only [NetLimitData.subseq_phi, Function.comp_apply,
        seqCenterD_subseq] using hsub
    · have hsub := hJbarconv.comp_tendsto_atTop hψ.tendsto_atTop
      simpa only [NetLimitData.subseq_phi, Function.comp_apply,
        seqCenterD_subseq] using hsub
  · intro alpha target k
    simpa only [NetLimitData.subseq_phi, Function.comp_apply,
      seqCenterD_subseq] using hsmooth alpha target (ψ k)

set_option maxHeartbeats 800000 in



theorem MetricCompactnessInputs.exists_supp_pts_fin
    (inp : MetricCompactnessInputs (I := I) X)
    (h8 : (8 : Real) < inp.normalRadius.gpRatio * inp.D)
    (hradD : 2 * item3RadiusFactor inp.decay inp.D < inp.D)
    (hradRatio : 2 * item3RadiusFactor inp.decay inp.D <
      inp.normalRadius.ratio * inp.D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P)
    (hstable : ∀ a b : Nat,
      (∀ᶠ k in Filter.atTop,
        BInter inp.decay inp.D P L.lamInf a b (L.φ k)) ∨
      (∀ᶠ k in Filter.atTop,
        ¬ BInter inp.decay inp.D P L.lamInf a b (L.φ k)))
    (r : Real) (hr : 0 ≤ r)
    (hconn : ∀ k : Nat,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M) :
    ∃ (phi : Nat → Nat) (hphi : StrictMono phi)
        (U : LiveSlot L inp.pack r → Set E)
        (C0 C1 : LiveSlot L inp.pack r → Set E)
        (aInf : (alpha : LiveSlot L inp.pack r) →
          Fin (inp.pack.A r) → E → Real)
        (Jinf : (alpha : LiveSlot L inp.pack r) →
          InterSlot L inp.pack r alpha → E → E)
        (Jbarinf : (alpha : LiveSlot L inp.pack r) →
          InterSlot L inp.pack r alpha → E → E),
      let Lphi := L.subseq hphi
      let beta := fun (n : Nat) (alpha : LiveSlot L inp.pack r) =>
        seqCenterD inp.decay P Lphi n (alpha.1 : Nat)
      let weightInf := fun (alpha : LiveSlot L inp.pack r) (z : E)
          (gamma : Fin (inp.pack.A r)) =>
        rawWeights
          (cutRaw
            (aInf alpha (baseIndex inp.decay inp.realizes inp.pack hr))
            (aInf alpha) (baseIndex inp.decay inp.realizes inp.pack hr))
          z gamma
      HasSuppConvData (I := I) inp P L r hr phi hphi U C0 C1
        aInf Jinf Jbarinf ∧
      ∀ᶠ n in Filter.atTop,
        let Y := X.obj (Lphi.φ n)
        letI : TopologicalSpace Y.M := Y.topology
        letI : ChartedSpace H Y.M := Y.charted
        letI : IsManifold I ∞ Y.M := Y.smooth
        letI : SigmaCompactSpace Y.M := Y.sigmaCompact
        letI : T2Space Y.M := Y.t2
        letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
        letI : ConnectedSpace Y.M := hconn (Lphi.φ n)
        letI : TopologicalSpace.MetrizableSpace Y.M :=
          Manifold.metrizableSpace I Y.M
        letI : T3Space Y.M := inferInstance
        letI : RiemannianBundle (fun x : Y.M => TangentSpace I x) :=
          ⟨Y.metric.toRiemannianMetric⟩
        letI : IsContinuousRiemannianBundle E
            (fun x : Y.M => TangentSpace I x) :=
          ⟨Y.metric.inner, Y.metric.contMDiff.continuous, fun _ _ _ => rfl⟩
        letI : MetricSpace Y.M := HopfRinow.riemMetricSpace (I := I) (M := Y.M)
        let chi := fun (alpha : LiveSlot L inp.pack r) =>
          NormalCoordinates.normalChartAt (I := I) Y.metric (beta n alpha)
        let sourcePatch : LiveSlot L inp.pack r → Set Y.M := fun alpha =>
          Lphi.hatSourceBall inp.decay P r n ∩
            (chi alpha).source ∩ (chi alpha) ⁻¹' U alpha
        let localWeight := fun (alpha : LiveSlot L inp.pack r)
            (x : Y.M) (gamma : Fin (inp.pack.A r)) =>
          weightInf alpha (chi alpha x) gamma
        let pairPts : (alpha : LiveSlot L inp.pack r) →
            InterSlot L inp.pack r alpha → Nat → Nat → Y.M → Y.M :=
          fun alpha target a b x =>
            (chi alpha).symm
              (normalTransition (I := I) (X.obj (Lphi.φ b))
                (beta b target.1) (beta b alpha)
                (normalTransition (I := I) (X.obj (Lphi.φ a))
                  (beta a alpha) (beta a target.1) (chi alpha x)))
        let pts := fun (alpha : LiveSlot L inp.pack r) =>
          totalPts (X := X) pairPts alpha
        HasCompactCover (Lphi.hatSourceBall inp.decay P r n) sourcePatch ∧
          Lphi.hatSourceBall inp.decay P r n ⊆
            ⋃ alpha : LiveSlot L inp.pack r, sourcePatch alpha ∧
          (∀ alpha,
            sourcePatch alpha ⊆
              Lphi.hatBall inp.decay inp.D P inp.pack r n alpha.1) ∧
          (∀ alpha,
            centerAverage.WeightDataOn (sourcePatch alpha)
              (fun _ : Fin (inp.pack.A r) => Set.univ)
              (localWeight alpha)) ∧
          ∀ alpha gamma epsilon, 0 < epsilon →
            ∃ N : Nat, ∀ a ≥ N, ∀ b ≥ N,
              ∀ x ∈ sourcePatch alpha,
                localWeight alpha x gamma ≠ 0 →
                  dist x (pts alpha a b x gamma) < epsilon := by
  classical
  obtain ⟨phi, hphi, U, C0, C1, aInf, Jinf, Jbarinf, hUopen, hU8,
      hC0, hC1, hC01, hC1U, hC0convex, hC0zero,
      hbuffer, hcore, hgeom, hlim, htrans, hstage,
      hsupp⟩ :=
    inp.exists_atom_supp_fin h8 hradD hradRatio P L hstable r hr
  obtain ⟨hgp0, _hrad⟩ := inp.item3ScaleTails h8 hradD hradRatio P L r
  have hgpPhi : Item3GpScaleTail (I := I) inp.decay inp.D P
      (L.subseq hphi) inp.pack r :=
    hgp0.subseq inp.decay inp.D P L inp.pack r hphi
  have hweightData : ∀ alpha : LiveSlot L inp.pack r,
      centerAverage.WeightDataOn (U alpha)
        (fun _ : Fin (inp.pack.A r) => Set.univ)
        (fun z gamma =>
          rawWeights
            (cutRaw
              (aInf alpha (baseIndex inp.decay inp.realizes inp.pack hr))
              (aInf alpha) (baseIndex inp.decay inp.realizes inp.pack hr))
            z gamma) := by
    intro alpha
    have hcoverU : ∀ᶠ k in Filter.atTop,
        letI : TopologicalSpace (X.obj ((L.subseq hphi).φ k)).M :=
          (X.obj ((L.subseq hphi).φ k)).topology
        letI : ChartedSpace H (X.obj ((L.subseq hphi).φ k)).M :=
          (X.obj ((L.subseq hphi).φ k)).charted
        letI : IsManifold I ∞ (X.obj ((L.subseq hphi).φ k)).M :=
          (X.obj ((L.subseq hphi).φ k)).smooth
        letI : T2Space (TangentBundle I (X.obj ((L.subseq hphi).φ k)).M) :=
          (X.obj ((L.subseq hphi).φ k)).t2TangentBundle
        Set.MapsTo
          (fun z => expMapDiffeo (I := I)
            (X.obj ((L.subseq hphi).φ k)).metric
            (seqCenterD inp.decay P (L.subseq hphi) k (alpha.1 : Nat)) z)
          (U alpha)
          (⋃ gamma : Fin (inp.pack.A r),
            (L.subseq hphi).innerBall inp.decay inp.D P inp.pack r k gamma) :=
      Filter.Eventually.of_forall fun k z hz => ((hgeom k).1 alpha).2.2 hz |>.2
    exact (hlim alpha).weight_data_of_innerCover hgpPhi hcoverU
  refine ⟨phi, hphi, U, C0, C1, aInf, Jinf, Jbarinf, ?_⟩
  dsimp only
  refine ⟨⟨hUopen, hU8, hC0, hC1, hC01, hC1U, hC0convex, hC0zero,
    hbuffer, hcore,
    hgeom, hlim, hweightData, htrans, hstage⟩, ?_⟩
  have hcenters : ∀ᶠ n in Filter.atTop, ∀ alpha : LiveSlot L inp.pack r,
      seqCenter inp.decay inp.D P ((L.subseq hphi).φ n) (alpha.1 : Nat) =
        some (seqCenterD inp.decay P (L.subseq hphi) n (alpha.1 : Nat)) :=
    Filter.eventually_all.mpr fun alpha =>
      seqCenterD_live inp.decay P (L.subseq hphi) (alpha.1 : Nat) (by
        simpa only [NetLimitData.subseq] using alpha.2)
  filter_upwards [hgpPhi, hcenters] with n hgpN hcenterN
  let Y := X.obj ((L.subseq hphi).φ n)
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : SigmaCompactSpace Y.M := Y.sigmaCompact
  letI : T2Space Y.M := Y.t2
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  letI : ConnectedSpace Y.M := hconn ((L.subseq hphi).φ n)
  letI : TopologicalSpace.MetrizableSpace Y.M :=
    Manifold.metrizableSpace I Y.M
  letI : T3Space Y.M := inferInstance
  letI : RiemannianBundle (fun x : Y.M => TangentSpace I x) :=
    ⟨Y.metric.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E
      (fun x : Y.M => TangentSpace I x) :=
    ⟨Y.metric.inner, Y.metric.contMDiff.continuous, fun _ _ _ => rfl⟩
  letI : MetricSpace Y.M := HopfRinow.riemMetricSpace (I := I) (M := Y.M)
  have hcover : (L.subseq hphi).hatSourceBall inp.decay P r n ⊆
      ⋃ alpha : LiveSlot L inp.pack r,
        (L.subseq hphi).hatSourceBall inp.decay P r n ∩
          (NormalCoordinates.normalChartAt (I := I) Y.metric
            (seqCenterD inp.decay P (L.subseq hphi) n
              (alpha.1 : Nat))).source ∩
          (NormalCoordinates.normalChartAt (I := I) Y.metric
            (seqCenterD inp.decay P (L.subseq hphi) n
              (alpha.1 : Nat))) ⁻¹' U alpha := by
    intro x hx
    rcases Set.mem_iUnion.mp ((hgeom n).2 hx) with ⟨alpha, z, hzU, rfl⟩
    refine Set.mem_iUnion.mpr ⟨alpha, ⟨hx, ?_⟩, ?_⟩
    · have hzball := ((hgeom n).1 alpha).2.1 hzU
      have hznorm : ‖z‖ < expMapC2Radius (I := I)
          (X.obj ((L.subseq hphi).φ n)).metric
          (seqCenterD inp.decay P (L.subseq hphi) n (alpha.1 : Nat)) := by
        simpa only [Metric.mem_ball, dist_zero_right] using hzball
      have hzsrc := mem_expMapDiffeo_source_of_norm_lt_radius (I := I)
        (X.obj ((L.subseq hphi).φ n)).metric
        (seqCenterD inp.decay P (L.subseq hphi) n (alpha.1 : Nat)) hznorm
      have hxtarget :=
        (expMapDiffeo (I := I) (X.obj ((L.subseq hphi).φ n)).metric
          (seqCenterD inp.decay P (L.subseq hphi) n (alpha.1 : Nat))).map_source hzsrc
      simpa only [normalChartAt_source_eq] using hxtarget
    · have hzball := ((hgeom n).1 alpha).2.1 hzU
      have hznorm : ‖z‖ < expMapC2Radius (I := I)
          (X.obj ((L.subseq hphi).φ n)).metric
          (seqCenterD inp.decay P (L.subseq hphi) n (alpha.1 : Nat)) := by
        simpa only [Metric.mem_ball, dist_zero_right] using hzball
      have hzsrc := mem_expMapDiffeo_source_of_norm_lt_radius (I := I)
        (X.obj ((L.subseq hphi).φ n)).metric
        (seqCenterD inp.decay P (L.subseq hphi) n (alpha.1 : Nat)) hznorm
      have hchart :
          NormalCoordinates.normalChartAt (I := I)
              (X.obj ((L.subseq hphi).φ n)).metric
              (seqCenterD inp.decay P (L.subseq hphi) n (alpha.1 : Nat))
              (expMapDiffeo (I := I) (X.obj ((L.subseq hphi).φ n)).metric
                (seqCenterD inp.decay P (L.subseq hphi) n (alpha.1 : Nat)) z) = z := by
        simpa only [normalChartAt] using
          (expMapDiffeo (I := I) (X.obj ((L.subseq hphi).φ n)).metric
            (seqCenterD inp.decay P (L.subseq hphi) n
              (alpha.1 : Nat))).left_inv hzsrc
      change NormalCoordinates.normalChartAt (I := I)
          (X.obj ((L.subseq hphi).φ n)).metric
          (seqCenterD inp.decay P (L.subseq hphi) n (alpha.1 : Nat))
          (expMapDiffeo (I := I) (X.obj ((L.subseq hphi).φ n)).metric
            (seqCenterD inp.decay P (L.subseq hphi) n (alpha.1 : Nat)) z) ∈ U alpha
      rw [hchart]
      exact hzU
  refine ⟨?_, hcover, ?_, ?_, ?_⟩
  · let chi := fun (alpha : LiveSlot L inp.pack r) =>
      NormalCoordinates.normalChartAt (I := I) Y.metric
        (seqCenterD inp.decay P (L.subseq hphi) n (alpha.1 : Nat))
    let sourceBall := (L.subseq hphi).hatSourceBall inp.decay P r n
    let sourcePatch : LiveSlot L inp.pack r → Set Y.M := fun alpha =>
      sourceBall ∩ (chi alpha).source ∩ (chi alpha) ⁻¹' U alpha
    let patchOpen : LiveSlot L inp.pack r → Set Y.M := fun alpha =>
      (chi alpha).source ∩ (chi alpha) ⁻¹' U alpha
    change HasCompactCover sourceBall sourcePatch
    have hopen : ∀ alpha, IsOpen (patchOpen alpha) := fun alpha =>
      (chi alpha).toOpenPartialHomeomorph.isOpen_inter_preimage (hUopen alpha)
    have hcoverOpen : sourceBall ⊆ ⋃ alpha, patchOpen alpha := by
      intro x hx
      rcases Set.mem_iUnion.mp (hcover hx) with ⟨alpha, hxalpha⟩
      exact Set.mem_iUnion.mpr ⟨alpha, ⟨hxalpha.1.2, hxalpha.2⟩⟩
    obtain ⟨K, hKcompact, hKsub, hKeq⟩ :=
      ((L.subseq hphi).hatSourceCompact inp.decay P r n).finite_compact_cover
        Finset.univ patchOpen (fun alpha _ => hopen alpha)
          (by simpa using hcoverOpen)
    refine ⟨K, hKcompact, ?_, ?_⟩
    · intro alpha x hxK
      have hxSource : x ∈ sourceBall := by
        change x ∈ (L.subseq hphi).hatSourceBall inp.decay P r n
        rw [hKeq]
        exact Set.mem_iUnion.mpr ⟨alpha,
          Set.mem_iUnion.mpr ⟨Finset.mem_univ alpha, hxK⟩⟩
      have hxOpen : x ∈ patchOpen alpha := hKsub alpha hxK
      exact ⟨⟨hxSource, hxOpen.1⟩, hxOpen.2⟩
    · simpa using hKeq
  · intro alpha x hx
    have hmap := ((hgeom n).1 alpha).2.2 hx.2
    have hexp : expMapDiffeo (I := I) Y.metric
        (seqCenterD inp.decay P (L.subseq hphi) n (alpha.1 : Nat))
        (NormalCoordinates.normalChartAt (I := I) Y.metric
          (seqCenterD inp.decay P (L.subseq hphi) n (alpha.1 : Nat)) x) = x := by
      simpa only [normalChartAt] using
        NormalCoordinates.normalChartAt_left_inv (I := I) Y.metric
          (seqCenterD inp.decay P (L.subseq hphi) n (alpha.1 : Nat))
          hx.1.2
    change expMapDiffeo (I := I) Y.metric
          (seqCenterD inp.decay P (L.subseq hphi) n (alpha.1 : Nat))
          (NormalCoordinates.normalChartAt (I := I) Y.metric
            (seqCenterD inp.decay P (L.subseq hphi) n (alpha.1 : Nat)) x) ∈
        (L.subseq hphi).hatBall inp.decay inp.D P inp.pack r n alpha.1 ∩
          ⋃ gamma : Fin (inp.pack.A r),
            (L.subseq hphi).innerBall inp.decay inp.D P inp.pack r n gamma
      at hmap
    rw [hexp] at hmap
    exact hmap.1
  · intro alpha
    simpa only [Set.preimage_univ] using
      (hweightData alpha).comp (fun _ hx => hx.2)
  · let chi := fun (alpha : LiveSlot L inp.pack r) =>
      NormalCoordinates.normalChartAt (I := I) Y.metric
        (seqCenterD inp.decay P (L.subseq hphi) n (alpha.1 : Nat))
    let sourcePatch : LiveSlot L inp.pack r → Set Y.M := fun alpha =>
      (L.subseq hphi).hatSourceBall inp.decay P r n ∩
        (chi alpha).source ∩ (chi alpha) ⁻¹' U alpha
    let localWeight := fun (alpha : LiveSlot L inp.pack r) (x : Y.M)
        (gamma : Fin (inp.pack.A r)) =>
      rawWeights
        (cutRaw
          (aInf alpha (baseIndex inp.decay inp.realizes inp.pack hr))
          (aInf alpha) (baseIndex inp.decay inp.realizes inp.pack hr))
        (chi alpha x) gamma
    let pairPts : (alpha : LiveSlot L inp.pack r) →
        InterSlot L inp.pack r alpha → Nat → Nat → Y.M → Y.M :=
      fun alpha target a b x =>
        (chi alpha).symm
          (normalTransition (I := I) (X.obj ((L.subseq hphi).φ b))
            (seqCenterD inp.decay P (L.subseq hphi) b
              (target.1.1 : Nat))
            (seqCenterD inp.decay P (L.subseq hphi) b (alpha.1 : Nat))
            (normalTransition (I := I) (X.obj ((L.subseq hphi).φ a))
              (seqCenterD inp.decay P (L.subseq hphi) a (alpha.1 : Nat))
              (seqCenterD inp.decay P (L.subseq hphi) a
                (target.1.1 : Nat))
              (chi alpha x)))
    let pts := fun (alpha : LiveSlot L inp.pack r) =>
      totalPts (X := X) pairPts alpha
    change ∀ alpha gamma epsilon, 0 < epsilon →
      ∃ N : Nat, ∀ a ≥ N, ∀ b ≥ N, ∀ x ∈ sourcePatch alpha,
        localWeight alpha x gamma ≠ 0 →
          dist x (pts alpha a b x gamma) < epsilon
    have hpair (alpha : LiveSlot L inp.pack r) :
        ∀ target : InterSlot L inp.pack r alpha, ∀ epsilon : Real,
          0 < epsilon → ∃ N : Nat, ∀ a ≥ N, ∀ b ≥ N,
            ∀ x ∈ sourcePatch alpha,
              localWeight alpha x target.1.1 ≠ 0 →
                dist x (pairPts alpha target a b x) < epsilon := by
      let centerAll : Fin (inp.pack.A r) → Y.M := fun gamma =>
        seqCenterD inp.decay P (L.subseq hphi) n (gamma : Nat)
      let pairWeight : Y.M → InterSlot L inp.pack r alpha → Real :=
        fun x target => localWeight alpha x target.1.1
      let centerPair : InterSlot L inp.pack r alpha → Y.M := fun _ =>
        seqCenterD inp.decay P (L.subseq hphi) n (alpha.1 : Nat)
      let sourceCage : InterSlot L inp.pack r alpha → Set Y.M := fun _ =>
        (L.subseq hphi).hatSourceCage inp.decay P inp.pack r n alpha.1
      let U8 : InterSlot L inp.pack r alpha → Set E := fun _ =>
        Metric.ball 0 (8 * L.lamInf (alpha.1 : Nat))
      let V6 : InterSlot L inp.pack r alpha → Set E := fun target =>
        Metric.closedBall 0 (6 * L.lamInf (target.1.1 : Nat))
      let V8 : InterSlot L inp.pack r alpha → Set E := fun target =>
        Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat))
      let B : InterSlot L inp.pack r alpha → Nat → E → E :=
        fun target k => normalTransition (I := I)
          (X.obj ((L.subseq hphi).φ k))
          (seqCenterD inp.decay P (L.subseq hphi) k (alpha.1 : Nat))
          (seqCenterD inp.decay P (L.subseq hphi) k
            (target.1.1 : Nat))
      let A : InterSlot L inp.pack r alpha → Nat → E → E :=
        fun target k => normalTransition (I := I)
          (X.obj ((L.subseq hphi).φ k))
          (seqCenterD inp.decay P (L.subseq hphi) k
            (target.1.1 : Nat))
          (seqCenterD inp.decay P (L.subseq hphi) k (alpha.1 : Nat))
      have hCageCompact : ∀ target : InterSlot L inp.pack r alpha,
          IsCompact (sourceCage target) := by
        intro target
        simpa only [sourceCage] using
          NetLimitData.hatCageCompact (I := I) (X := X) inp.decay P
            (L.subseq hphi) inp.pack r n alpha.1
      have hSuppCage : ∀ target : InterSlot L inp.pack r alpha,
          ∀ x : Y.M, x ∈ sourcePatch alpha → pairWeight x target ≠ 0 →
            x ∈ sourceCage target := by
        intro target x hx _hne
        have hmap := ((hgeom n).1 alpha).2.2 hx.2
        have hexp : expMapDiffeo (I := I) Y.metric
            (seqCenterD inp.decay P (L.subseq hphi) n (alpha.1 : Nat))
            (chi alpha x) = x := by
          simpa only [chi, normalChartAt] using
            NormalCoordinates.normalChartAt_left_inv (I := I) Y.metric
              (seqCenterD inp.decay P (L.subseq hphi) n (alpha.1 : Nat))
              hx.1.2
        change expMapDiffeo (I := I) Y.metric
            (seqCenterD inp.decay P (L.subseq hphi) n (alpha.1 : Nat))
            (chi alpha x) ∈
          (L.subseq hphi).hatBall inp.decay inp.D P inp.pack r n alpha.1 ∩
            ⋃ gamma : Fin (inp.pack.A r),
              (L.subseq hphi).innerBall inp.decay inp.D P inp.pack r n gamma
          at hmap
        rw [hexp] at hmap
        exact NetLimitData.hatCageSub (I := I) (X := X) inp.decay P
          (L.subseq hphi) inp.pack r n alpha.1 ⟨hx.1.1, hmap.1⟩
      have hR : 4 * L.lamInf (alpha.1 : Nat) <
          expRadiusGp (I := I) Y.metric
            (seqCenterD inp.decay P (L.subseq hphi) n (alpha.1 : Nat)) :=
        hgpN alpha.1 _ (hcenterN alpha)
      have hsrc : ∀ target : InterSlot L inp.pack r alpha,
          sourceCage target ⊆ (chi alpha).source := by
        intro target
        simpa only [sourceCage, chi, centerAll] using
          NetLimitData.hatCageSrcOfRad (I := I) (X := X) inp.decay P
            (L.subseq hphi) inp.pack r n centerAll alpha.1
            (hcenterN alpha) hR
      have hBcont : ∀ target : InterSlot L inp.pack r alpha,
          ContinuousOn (Jinf alpha target) (U8 target) := by
        intro target
        simpa only [U8] using (htrans alpha target).2.2.1
      have hsigma : 4 * L.lamInf (alpha.1 : Nat) /
            Real.sqrt (gpCoerciveConst (I := I) Y.metric
              (seqCenterD inp.decay P (L.subseq hphi) n
                (alpha.1 : Nat))) <
          8 * L.lamInf (alpha.1 : Nat) := by
        have hhalf : (1 / 2 : Real) ≤ gpCoerciveConst (I := I) Y.metric
            (seqCenterD inp.decay P (L.subseq hphi) n (alpha.1 : Nat)) :=
          inp.normalBounds.half_le_gpConst ((L.subseq hphi).φ n)
            (seqCenterD inp.decay P (L.subseq hphi) n (alpha.1 : Nat))
        have hsqrtHalf : (1 / 2 : Real) < Real.sqrt (1 / 2 : Real) := by
          have hs := Real.sq_sqrt (by norm_num : (0 : Real) ≤ 1 / 2)
          have hn := Real.sqrt_nonneg (1 / 2 : Real)
          nlinarith
        have hsqrt : (1 / 2 : Real) < Real.sqrt
            (gpCoerciveConst (I := I) Y.metric
              (seqCenterD inp.decay P (L.subseq hphi) n
                (alpha.1 : Nat))) :=
          hsqrtHalf.trans_le (Real.sqrt_le_sqrt hhalf)
        have hsc : 0 < Real.sqrt (gpCoerciveConst (I := I) Y.metric
            (seqCenterD inp.decay P (L.subseq hphi) n
              (alpha.1 : Nat))) :=
          Real.sqrt_pos.mpr (gpCoerciveConst_pos (I := I) Y.metric
            (seqCenterD inp.decay P (L.subseq hphi) n (alpha.1 : Nat)))
        have hlam : 0 < L.lamInf (alpha.1 : Nat) :=
          inp.decay.lambda_pos inp.hD (L.rInf (alpha.1 : Nat))
        apply (div_lt_iff₀ hsc).2
        have hfour : (4 : Real) < 8 * Real.sqrt
            (gpCoerciveConst (I := I) Y.metric
              (seqCenterD inp.decay P (L.subseq hphi) n
                (alpha.1 : Nat))) := by
          nlinarith
        calc
          4 * L.lamInf (alpha.1 : Nat) <
              (8 * Real.sqrt (gpCoerciveConst (I := I) Y.metric
                (seqCenterD inp.decay P (L.subseq hphi) n
                  (alpha.1 : Nat)))) * L.lamInf (alpha.1 : Nat) :=
            mul_lt_mul_of_pos_right hfour hlam
          _ = (8 * L.lamInf (alpha.1 : Nat)) *
              Real.sqrt (gpCoerciveConst (I := I) Y.metric
                (seqCenterD inp.decay P (L.subseq hphi) n
                  (alpha.1 : Nat))) := by ring
      have hKU : ∀ target : InterSlot L inp.pack r alpha,
          (chi alpha) '' sourceCage target ⊆ U8 target := by
        intro target
        simpa only [chi, sourceCage, U8, centerAll] using
          hatCageImg' (I := I) (X := X) inp.decay P (L.subseq hphi)
            inp.pack r n centerAll alpha.1
            (fun gamma => 8 * L.lamInf (gamma : Nat))
            (hcenterN alpha) hR hsigma
      have hSuppV : ∀ target : InterSlot L inp.pack r alpha,
          ∀ x : Y.M, x ∈ sourcePatch alpha → pairWeight x target ≠ 0 →
            Jinf alpha target (chi alpha x) ∈ V6 target := by
        intro target x hx hne
        obtain ⟨target', hslot, hmem⟩ :=
          hsupp alpha (chi alpha x) hx.2 target.1.1 (by
            simpa only [pairWeight] using hne)
        have htarget : target' = target := by
          apply Subtype.ext
          apply Subtype.ext
          exact hslot
        simpa only [V6, htarget] using hmem
      obtain ⟨sourceK, hK, hSuppK, hsrcK, hKU_K, hKV6⟩ :=
        NetLimitData.hatSuppCageData (I := I) (X := X) inp.decay P
          (L.subseq hphi) inp.pack r n (s := sourcePatch alpha)
          pairWeight centerPair sourceCage U8 V6 (Jinf alpha)
          hCageCompact hSuppCage (by
            intro target
            simpa only [centerPair] using hsrc target)
          hBcont (by
            intro target
            simpa only [centerPair] using hKU target)
          (fun _ => Metric.isClosed_closedBall) (by
            intro target x hx hne
            simpa only [centerPair] using hSuppV target x hx hne)
      have hKV8 : ∀ target : InterSlot L inp.pack r alpha, ∀ v : E,
          v ∈ (chi alpha) '' sourceK target →
            Jinf alpha target v ∈ V8 target := by
        intro target v hv
        have hv6 := hKV6 target v (by
          simpa only [centerPair] using hv)
        change Jinf alpha target v ∈ Metric.closedBall 0
          (6 * L.lamInf (target.1.1 : Nat)) at hv6
        rw [Metric.mem_closedBall, dist_zero_right] at hv6
        change Jinf alpha target v ∈
          Metric.ball 0 (8 * L.lamInf (target.1.1 : Nat))
        rw [Metric.mem_ball, dist_zero_right]
        have hlam : 0 < L.lamInf (target.1.1 : Nat) :=
          inp.decay.lambda_pos inp.hD (L.rInf (target.1.1 : Nat))
        nlinarith
      have hpoints := NetLimitData.hatSuppPtsOfComp (I := I) (X := X)
        inp.decay P (L.subseq hphi) inp.pack r n (s := sourcePatch alpha)
        pairWeight centerPair sourceK U8 V8 B (Jinf alpha) A (Jbarinf alpha)
        (hconn ((L.subseq hphi).φ n)) hK hSuppK hsrcK
        (fun _ => Metric.isOpen_ball)
        (fun target => by simpa only [B, U8] using
          (htrans alpha target).2.2.2.2.1)
        (fun target => by simpa only [A, V8] using
          (htrans alpha target).2.2.2.2.2.1)
        hBcont
        (fun target => by simpa only [V8] using
          (htrans alpha target).2.2.2.1)
        (fun target => by simpa only [U8, V8] using
          (htrans alpha target).2.2.2.2.2.2.1)
        hKU_K (by
          intro target v hv
          simpa only [centerPair] using hKV8 target v (by
            simpa only [centerPair] using hv))
      intro target epsilon hepsilon
      simpa only [pairWeight, centerPair, B, A, pairPts, chi] using
        hpoints target epsilon hepsilon
    intro alpha gamma epsilon hepsilon
    by_cases htarget : ∃ target : InterSlot L inp.pack r alpha,
        target.1.1 = gamma
    · let target := Classical.choose htarget
      have hslot : target.1.1 = gamma := Classical.choose_spec htarget
      obtain ⟨N, hN⟩ := hpair alpha target epsilon hepsilon
      refine ⟨N, ?_⟩
      intro a ha b hb x hx hne
      have hp := hN a ha b hb x hx (by simpa only [hslot] using hne)
      have hlookup : interSlot? alpha gamma = some target := by
        unfold interSlot?
        split
        next h =>
          congr 1
        next h =>
          exact (h htarget).elim
      simpa only [pts, totalPts, hlookup] using hp
    · refine ⟨0, ?_⟩
      intro a _ha b _hb x hx hne
      exfalso
      obtain ⟨target, hslot, _hmem⟩ := hsupp alpha (chi alpha x) hx.2 gamma hne
      exact htarget ⟨target, hslot⟩

set_option maxHeartbeats 800000 in





theorem stepCJoinFixed (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : forall k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P)
    (pb : hd.PackingBound D) (r : Real) (n : Nat)
    (rho :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : MetricSpace (X.obj (L.φ n)).M := (P (L.φ n)).ms
      SmoothPartitionOfUnity (Fin (pb.A r)) I (X.obj (L.φ n)).M
        (Metric.closedBall (X.obj (L.φ n)).basepoint r))
    (hrho :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : MetricSpace (X.obj (L.φ n)).M := (P (L.φ n)).ms
      rho.IsSubordinate (fun gamma : Fin (pb.A r) =>
        (NetLimitData.hatBall (I := I) (X := X) (hd := hd) (D := D)
          (P := P) (L := L) (pb := pb) (r := r) (k := n) (γ := gamma) :
          Set (X.obj (L.φ n)).M)))
    (join : (X.obj (L.φ n)).M -> (X.obj (L.φ n)).M -> Real -> (X.obj (L.φ n)).M)
    (radSeq : Nat -> Nat -> (X.obj (L.φ n)).M -> Real)
    (center : Fin (pb.A r) -> (X.obj (L.φ n)).M)
    (U V : Fin (pb.A r) -> Set E)
    (B : Fin (pb.A r) -> Nat -> E -> E)
    (Binf : Fin (pb.A r) -> E -> E)
    (A : Fin (pb.A r) -> Nat -> E -> E)
    (Ainf : Fin (pb.A r) -> E -> E)
    (hconn :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      ConnectedSpace (X.obj (L.φ n)).M)
    (hX : SeqMetricComplete (I := I) X)
    (hcenter : forall gamma : Fin (pb.A r),
      seqCenter hd D P (L.φ n) (gamma : Nat) = some (center gamma))
    (hgp : Item3GpScaleAt (I := I) hd D P L pb r n)
    (hrad : forall a b : Nat, forall x : (X.obj (L.φ n)).M,
      x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n -> 0 < radSeq a b x)
    (hactive_mem :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) := (X.obj (L.φ n)).t2TangentBundle
      letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
      letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
        Manifold.metrizableSpace I (X.obj (L.φ n)).M
      letI : T3Space (X.obj (L.φ n)).M := inferInstance
      letI : RiemannianBundle (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
        ⟨(X.obj (L.φ n)).metric.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
        ⟨(X.obj (L.φ n)).metric.inner, (X.obj (L.φ n)).metric.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace (X.obj (L.φ n)).M := HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
      let ptsSeq := NetLimitData.decodedCompPts (I := I) (X.obj (L.φ n)).metric center B A
      forall a b : Nat, forall x : (X.obj (L.φ n)).M,
        x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
          forall gamma : Fin (pb.A r), rho gamma x ≠ 0 ->
            dist x (ptsSeq a b x gamma) < radSeq a b x)
    (hstrict :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) := (X.obj (L.φ n)).t2TangentBundle
      letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
      letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
        Manifold.metrizableSpace I (X.obj (L.φ n)).M
      letI : T3Space (X.obj (L.φ n)).M := inferInstance
      let ptsSeq := NetLimitData.decodedCompPts (I := I) (X.obj (L.φ n)).metric center B A
      forall a b : Nat, forall x : (X.obj (L.φ n)).M,
        x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
          StrictDistInput (I := I) (X.obj (L.φ n)).metric
            (centerAverage.activeFill
              (fun y : (X.obj (L.φ n)).M => fun gamma : Fin (pb.A r) => rho gamma y)
              (ptsSeq a b) (fun y : (X.obj (L.φ n)).M => y) x)
            join x (radSeq a b x))
    (hVopen : forall gamma : Fin (pb.A r), IsOpen (V gamma))
    (hB : forall gamma : Fin (pb.A r), MapCInfConvOnCompacts (U gamma) (B gamma) (Binf gamma))
    (hA : forall gamma : Fin (pb.A r), MapCInfConvOnCompacts (V gamma) (A gamma) (Ainf gamma))
    (hBcont : forall gamma : Fin (pb.A r), ContinuousOn (Binf gamma) (U gamma))
    (hAcont : forall gamma : Fin (pb.A r), ContinuousOn (Ainf gamma) (V gamma))
    (hid : forall gamma : Fin (pb.A r), forall v : E, v ∈ U gamma ->
      Binf gamma v ∈ V gamma -> Ainf gamma (Binf gamma v) = v)
    (hKU :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) := (X.obj (L.φ n)).t2TangentBundle
      forall gamma : Fin (pb.A r),
        (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric (center gamma)) ''
            NetLimitData.hatSourceCage (I := I) (X := X) hd P L pb r n gamma ⊆ U gamma)
    (V' : Fin (pb.A r) -> Set E)
    (hV'closed : forall gamma : Fin (pb.A r), IsClosed (V' gamma))
    (hV'sub : forall gamma : Fin (pb.A r), V' gamma ⊆ V gamma)
    (hKV0 :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) := (X.obj (L.φ n)).t2TangentBundle
      forall gamma : Fin (pb.A r), forall v : E,
        v ∈ (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric (center gamma)) ''
            NetLimitData.hatSourceCage (I := I) (X := X) hd P L pb r n gamma ->
        forall a : Nat, B gamma a v ∈ V' gamma) :
    let hcomplete := NetLimitData.sourceComplete (I := I) (X := X) hd P L n hX hconn
    letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
    letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
    letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
    letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
    letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
    letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) := (X.obj (L.φ n)).t2TangentBundle
    letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
    letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
      Manifold.metrizableSpace I (X.obj (L.φ n)).M
    letI : T3Space (X.obj (L.φ n)).M := inferInstance
    letI : RiemannianBundle (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
      ⟨(X.obj (L.φ n)).metric.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
      ⟨(X.obj (L.φ n)).metric.inner, (X.obj (L.φ n)).metric.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace (X.obj (L.φ n)).M := HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
    let ptsSeq := NetLimitData.decodedCompPts (I := I) (X.obj (L.φ n)).metric center B A
    forall eps : Real, eps > 0 -> exists N : Nat,
      forall a : Nat, a >= N -> forall b : Nat, b >= N ->
        forall x : (X.obj (L.φ n)).M,
          x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
            dist x
              (centerAverageOn (I := I) (X.obj (L.φ n)).metric
                (NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n)
                (fun y : (X.obj (L.φ n)).M => fun gamma : Fin (pb.A r) => rho gamma y)
                (centerAverage.activeFill
                  (fun y : (X.obj (L.φ n)).M => fun gamma : Fin (pb.A r) => rho gamma y)
                  (ptsSeq a b) (fun y : (X.obj (L.φ n)).M => y))
                join (fun y : (X.obj (L.φ n)).M => y) (radSeq a b)
                (fun y : (X.obj (L.φ n)).M => y)
                (fun y hy => centerAverage.inputOfFillSelf (I := I)
                  (g := (X.obj (L.φ n)).metric)
                  (μ := fun y : (X.obj (L.φ n)).M => fun gamma : Fin (pb.A r) => rho gamma y)
                  (pts := ptsSeq a b) (join := join)
                  (r := radSeq a b) (qstar := fun y : (X.obj (L.φ n)).M => y)
                  y hcomplete (hrad a b y hy) (hactive_mem a b y hy)
                  ((NetLimitData.hatPOUDataTwo (I := I) (X := X) (hd := hd)
                    (D := D) (P := P) (L := L) (pb := pb) (r := r) (n := n)
                    (rho := rho) (hrho := hrho) a b hy).1.1)
                  ((NetLimitData.hatPOUDataTwo (I := I) (X := X) (hd := hd)
                    (D := D) (P := P) (L := L) (pb := pb) (r := r) (n := n)
                    (rho := rho) (hrho := hrho) a b hy).1.2.1)
                  (hstrict a b y hy)) x) < eps := by
  exact NetLimitData.unifHatCageSelfComp hd P L pb r n rho hrho join radSeq center U V
    B Binf A Ainf hconn hX hcenter
    (fun gamma => hgp gamma (center gamma) (hcenter gamma))
    hrad hactive_mem hstrict hVopen hB hA hBcont hAcont hid hKU
    (fun gamma v hv =>
      hV'sub gamma (binfMemClosed (hB gamma) (hKU gamma hv) (hV'closed gamma)
        (Filter.Eventually.of_forall (hKV0 gamma v hv))))

set_option maxHeartbeats 800000 in




theorem stepCJoinDataFixed (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : forall k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P)
    (pb : hd.PackingBound D) (r : Real) (n : Nat)
    (mu : (X.obj (L.φ n)).M -> Fin (pb.A r) -> Real)
    (hmu :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : MetricSpace (X.obj (L.φ n)).M := (P (L.φ n)).ms
      centerAverage.WeightDataOn
        (NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n)
        (fun gamma : Fin (pb.A r) =>
          (NetLimitData.hatBall (I := I) (X := X) (hd := hd) (D := D)
            (P := P) (L := L) (pb := pb) (r := r) (k := n) (γ := gamma) :
            Set (X.obj (L.φ n)).M)) mu)
    (join : (X.obj (L.φ n)).M -> (X.obj (L.φ n)).M -> Real ->
      (X.obj (L.φ n)).M)
    (radSeq : Nat -> Nat -> (X.obj (L.φ n)).M -> Real)
    (center : Fin (pb.A r) -> (X.obj (L.φ n)).M)
    (U V : Fin (pb.A r) -> Set E)
    (B : Fin (pb.A r) -> Nat -> E -> E)
    (Binf : Fin (pb.A r) -> E -> E)
    (A : Fin (pb.A r) -> Nat -> E -> E)
    (Ainf : Fin (pb.A r) -> E -> E)
    (hconn :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      ConnectedSpace (X.obj (L.φ n)).M)
    (hX : SeqMetricComplete (I := I) X)
    (hcenter : forall gamma : Fin (pb.A r),
      seqCenter hd D P (L.φ n) (gamma : Nat) = some (center gamma))
    (hgp : Item3GpScaleAt (I := I) hd D P L pb r n)
    (hrad : forall a b : Nat, forall x : (X.obj (L.φ n)).M,
      x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n -> 0 < radSeq a b x)
    (hactive_mem :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) := (X.obj (L.φ n)).t2TangentBundle
      letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
      letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
        Manifold.metrizableSpace I (X.obj (L.φ n)).M
      letI : T3Space (X.obj (L.φ n)).M := inferInstance
      letI : RiemannianBundle (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
        ⟨(X.obj (L.φ n)).metric.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
        ⟨(X.obj (L.φ n)).metric.inner, (X.obj (L.φ n)).metric.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace (X.obj (L.φ n)).M := HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
      let ptsSeq := NetLimitData.decodedCompPts (I := I) (X.obj (L.φ n)).metric center B A
      forall a b : Nat, forall x : (X.obj (L.φ n)).M,
        x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
          forall gamma : Fin (pb.A r), mu x gamma ≠ 0 ->
            dist x (ptsSeq a b x gamma) < radSeq a b x)
    (hstrict :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) := (X.obj (L.φ n)).t2TangentBundle
      letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
      letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
        Manifold.metrizableSpace I (X.obj (L.φ n)).M
      letI : T3Space (X.obj (L.φ n)).M := inferInstance
      let ptsSeq := NetLimitData.decodedCompPts (I := I) (X.obj (L.φ n)).metric center B A
      forall a b : Nat, forall x : (X.obj (L.φ n)).M,
        x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
          StrictDistInput (I := I) (X.obj (L.φ n)).metric
            (centerAverage.activeFill mu (ptsSeq a b)
              (fun y : (X.obj (L.φ n)).M => y) x)
            join x (radSeq a b x))
    (hVopen : forall gamma : Fin (pb.A r), IsOpen (V gamma))
    (hB : forall gamma : Fin (pb.A r), MapCInfConvOnCompacts (U gamma) (B gamma) (Binf gamma))
    (hA : forall gamma : Fin (pb.A r), MapCInfConvOnCompacts (V gamma) (A gamma) (Ainf gamma))
    (hBcont : forall gamma : Fin (pb.A r), ContinuousOn (Binf gamma) (U gamma))
    (hAcont : forall gamma : Fin (pb.A r), ContinuousOn (Ainf gamma) (V gamma))
    (hid : forall gamma : Fin (pb.A r), forall v : E, v ∈ U gamma ->
      Binf gamma v ∈ V gamma -> Ainf gamma (Binf gamma v) = v)
    (hKU :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) := (X.obj (L.φ n)).t2TangentBundle
      forall gamma : Fin (pb.A r),
        (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric (center gamma)) ''
            NetLimitData.hatSourceCage (I := I) (X := X) hd P L pb r n gamma ⊆ U gamma)
    (V' : Fin (pb.A r) -> Set E)
    (hV'closed : forall gamma : Fin (pb.A r), IsClosed (V' gamma))
    (hV'sub : forall gamma : Fin (pb.A r), V' gamma ⊆ V gamma)
    (hKV0 :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) := (X.obj (L.φ n)).t2TangentBundle
      forall gamma : Fin (pb.A r), forall v : E,
        v ∈ (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric (center gamma)) ''
            NetLimitData.hatSourceCage (I := I) (X := X) hd P L pb r n gamma ->
        forall a : Nat, B gamma a v ∈ V' gamma) :
    let hcomplete := NetLimitData.sourceComplete (I := I) (X := X) hd P L n hX hconn
    letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
    letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
    letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
    letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
    letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
    letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) := (X.obj (L.φ n)).t2TangentBundle
    letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
    letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
      Manifold.metrizableSpace I (X.obj (L.φ n)).M
    letI : T3Space (X.obj (L.φ n)).M := inferInstance
    letI : RiemannianBundle (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
      ⟨(X.obj (L.φ n)).metric.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
      ⟨(X.obj (L.φ n)).metric.inner, (X.obj (L.φ n)).metric.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace (X.obj (L.φ n)).M := HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
    let ptsSeq := NetLimitData.decodedCompPts (I := I) (X.obj (L.φ n)).metric center B A
    forall eps : Real, eps > 0 -> exists N : Nat,
      forall a : Nat, a >= N -> forall b : Nat, b >= N ->
        forall x : (X.obj (L.φ n)).M,
          x ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
            dist x
              (centerAverageOn (I := I) (X.obj (L.φ n)).metric
                (NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n)
                mu
                (centerAverage.activeFill mu (ptsSeq a b)
                  (fun y : (X.obj (L.φ n)).M => y))
                join (fun y : (X.obj (L.φ n)).M => y) (radSeq a b)
                (fun y : (X.obj (L.φ n)).M => y)
                (fun y hy => centerAverage.inputOfFillSelf (I := I)
                  (g := (X.obj (L.φ n)).metric) (μ := mu)
                  (pts := ptsSeq a b) (join := join)
                  (r := radSeq a b) (qstar := fun y : (X.obj (L.φ n)).M => y)
                  y hcomplete (hrad a b y hy) (hactive_mem a b y hy)
                  ((hmu.data hy).1.1) ((hmu.data hy).1.2.1)
                  (hstrict a b y hy)) x) < eps := by
  exact NetLimitData.unifHatCageData hd P L pb r n mu hmu join radSeq center U V
    B Binf A Ainf hconn hX hcenter
    (fun gamma => hgp gamma (center gamma) (hcenter gamma))
    hrad hactive_mem hstrict hVopen hB hA hBcont hAcont hid hKU
    (fun gamma v hv =>
      hV'sub gamma (binfMemClosed (hB gamma) (hKU gamma hv) (hV'closed gamma)
        (Filter.Eventually.of_forall (hKV0 gamma v hv))))











theorem stepCJoin (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : forall k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : DifferentialGeometry.HCGCompactness.NetLimitData (X := X) hd D P)
    (pb : hd.PackingBound D) (r : Real) (n : Nat)
    (metricInput : NormalCoordMetricBoundInput (I := I) X)
    (x y : Fin (pb.A r) -> forall k : Nat, (X.obj (L.φ k)).M)
    (U V Ua Va : Fin (pb.A r) -> Set E)
    (rho :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : MetricSpace (X.obj (L.φ n)).M := (P (L.φ n)).ms
      SmoothPartitionOfUnity (Fin (pb.A r)) I (X.obj (L.φ n)).M
        (Metric.closedBall (X.obj (L.φ n)).basepoint r))
    (hrho :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : MetricSpace (X.obj (L.φ n)).M := (P (L.φ n)).ms
      rho.IsSubordinate (fun gamma : Fin (pb.A r) =>
        (NetLimitData.hatBall (I := I) (X := X) (hd := hd) (D := D)
          (P := P) (L := L) (pb := pb) (r := r) (k := n) (γ := gamma) :
          Set (X.obj (L.φ n)).M)))
    (join : (X.obj (L.φ n)).M -> (X.obj (L.φ n)).M -> Real -> (X.obj (L.φ n)).M)
    (radSeq : Nat -> Nat -> (X.obj (L.φ n)).M -> Real)
    (hconn :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      ConnectedSpace (X.obj (L.φ n)).M)
    (hX : SeqMetricComplete (I := I) X)
    (hgp : Item3GpScaleAt (I := I) hd D P L pb r n)
    (hcenter : forall gamma : Fin (pb.A r),
      seqCenter hd D P (L.φ n) (gamma : Nat) = some (x gamma n))
    (hrad : forall a b : Nat, forall xx : (X.obj (L.φ n)).M,
      xx ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n -> 0 < radSeq a b xx)
    (hU : forall gamma : Fin (pb.A r), IsOpen (U gamma))
    (hVopen : forall gamma : Fin (pb.A r), IsOpen (V gamma))
    (hUa : forall gamma : Fin (pb.A r), IsOpen (Ua gamma))
    (hVa : forall gamma : Fin (pb.A r), IsOpen (Va gamma))
    (hUanorm : forall gamma : Fin (pb.A r),
      ∃ Z : Real, ∀ z ∈ Ua gamma, ‖z‖ ≤ Z)
    (hVanorm : forall gamma : Fin (pb.A r),
      ∃ Z : Real, ∀ z ∈ Va gamma, ‖z‖ ≤ Z)
    (hUmetric : forall gamma : Fin (pb.A r), ∀ᶠ k in atTop,
      U gamma ⊆ Metric.ball (0 : E)
        (metricInput.radius (L.φ k) (x gamma k)))
    (hVmetric : forall gamma : Fin (pb.A r), ∀ᶠ k in atTop,
      V gamma ⊆ Metric.ball (0 : E)
        (metricInput.radius (L.φ k) (y gamma k)))
    (hUametric : forall gamma : Fin (pb.A r), ∀ᶠ k in atTop,
      Ua gamma ⊆ Metric.ball (0 : E)
        (metricInput.radius (L.φ k) (x gamma k)))
    (hVametric : forall gamma : Fin (pb.A r), ∀ᶠ k in atTop,
      Va gamma ⊆ Metric.ball (0 : E)
        (metricInput.radius (L.φ k) (y gamma k)))
    (hUexp : forall gamma : Fin (pb.A r), ∀ᶠ k in atTop,
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
        (X.obj (L.φ k)).t2TangentBundle
      U gamma ⊆ Metric.ball (0 : E)
        (expMapC2Radius (I := I) (X.obj (L.φ k)).metric (x gamma k)))
    (hVexp : forall gamma : Fin (pb.A r), ∀ᶠ k in atTop,
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
        (X.obj (L.φ k)).t2TangentBundle
      V gamma ⊆ Metric.ball (0 : E)
        (expMapC2Radius (I := I) (X.obj (L.φ k)).metric (y gamma k)))
    (hUaexp : forall gamma : Fin (pb.A r), ∀ᶠ k in atTop,
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
        (X.obj (L.φ k)).t2TangentBundle
      Ua gamma ⊆ Metric.ball (0 : E)
        (expMapC2Radius (I := I) (X.obj (L.φ k)).metric (x gamma k)))
    (hVaexp : forall gamma : Fin (pb.A r), ∀ᶠ k in atTop,
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
        (X.obj (L.φ k)).t2TangentBundle
      Va gamma ⊆ Metric.ball (0 : E)
        (expMapC2Radius (I := I) (X.obj (L.φ k)).metric (y gamma k)))
    (hJ : forall gamma : Fin (pb.A r), ∀ᶠ k in atTop,
      ContDiffOn Real (⊤ : ℕ∞)
        (normalTransition (I := I) (X.obj (L.φ k)) (x gamma k) (y gamma k))
        (U gamma))
    (hJbar : forall gamma : Fin (pb.A r), ∀ᶠ k in atTop,
      ContDiffOn Real (⊤ : ℕ∞)
        (normalTransition (I := I) (X.obj (L.φ k)) (y gamma k) (x gamma k))
        (V gamma))
    (hovlJ : forall gamma : Fin (pb.A r), ∀ᶠ k in atTop,
      NormalOverlapOn (I := I) (X.obj (L.φ k)) (x gamma k) (y gamma k) (U gamma))
    (hovlJbar : forall gamma : Fin (pb.A r), ∀ᶠ k in atTop,
      NormalOverlapOn (I := I) (X.obj (L.φ k)) (y gamma k) (x gamma k) (V gamma))
    (hmapJ : forall gamma : Fin (pb.A r), ∀ᶠ k in atTop,
      Set.MapsTo
        (normalTransition (I := I) (X.obj (L.φ k)) (x gamma k) (y gamma k))
        (U gamma) (Va gamma))
    (hmapJbar : forall gamma : Fin (pb.A r), ∀ᶠ k in atTop,
      Set.MapsTo
        (normalTransition (I := I) (X.obj (L.φ k)) (y gamma k) (x gamma k))
        (V gamma) (Ua gamma))
    (hLeft : forall gamma : Fin (pb.A r), ∀ᶠ k in atTop, forall z, z ∈ U gamma ->
      normalTransition (I := I) (X.obj (L.φ k)) (y gamma k) (x gamma k)
        (normalTransition (I := I) (X.obj (L.φ k)) (x gamma k) (y gamma k) z) = z)
    (hRight : forall gamma : Fin (pb.A r), ∀ᶠ k in atTop, forall w, w ∈ V gamma ->
      normalTransition (I := I) (X.obj (L.φ k)) (x gamma k) (y gamma k)
        (normalTransition (I := I) (X.obj (L.φ k)) (y gamma k) (x gamma k) w) = w)
    (hactive0 :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) := (X.obj (L.φ n)).t2TangentBundle
      letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
      letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
        Manifold.metrizableSpace I (X.obj (L.φ n)).M
      letI : T3Space (X.obj (L.φ n)).M := inferInstance
      letI : RiemannianBundle (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
        ⟨(X.obj (L.φ n)).metric.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
        ⟨(X.obj (L.φ n)).metric.inner, (X.obj (L.φ n)).metric.contMDiff.continuous, fun _ _ _ => rfl⟩
      letI : MetricSpace (X.obj (L.φ n)).M := HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
      forall a b : Nat, forall xx : (X.obj (L.φ n)).M,
        xx ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
          forall gamma : Fin (pb.A r), rho gamma xx ≠ 0 ->
            dist xx (NetLimitData.decodedCompPts (I := I) (X.obj (L.φ n)).metric
              (fun gamma => x gamma n)
              (fun gamma a => normalTransition (I := I) (X.obj (L.φ a)) (x gamma a) (y gamma a))
              (fun gamma b => normalTransition (I := I) (X.obj (L.φ b)) (y gamma b) (x gamma b))
              a b xx gamma) < radSeq a b xx)
    (hstrict0 :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) := (X.obj (L.φ n)).t2TangentBundle
      letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
      letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
        Manifold.metrizableSpace I (X.obj (L.φ n)).M
      letI : T3Space (X.obj (L.φ n)).M := inferInstance
      forall a b : Nat, forall xx : (X.obj (L.φ n)).M,
        xx ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
          StrictDistInput (I := I) (X.obj (L.φ n)).metric
            (centerAverage.activeFill
              (fun yy : (X.obj (L.φ n)).M => fun gamma : Fin (pb.A r) => rho gamma yy)
              (NetLimitData.decodedCompPts (I := I) (X.obj (L.φ n)).metric
                (fun gamma => x gamma n)
                (fun gamma a => normalTransition (I := I) (X.obj (L.φ a)) (x gamma a) (y gamma a))
                (fun gamma b => normalTransition (I := I) (X.obj (L.φ b)) (y gamma b) (x gamma b))
                a b)
              (fun yy : (X.obj (L.φ n)).M => yy) xx)
            join xx (radSeq a b xx))
    (hKU :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) := (X.obj (L.φ n)).t2TangentBundle
      forall gamma : Fin (pb.A r),
        (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric (x gamma n)) ''
            NetLimitData.hatSourceCage (I := I) (X := X) hd P L pb r n gamma ⊆ U gamma)
    (V' : Fin (pb.A r) -> Set E)
    (hV'closed : forall gamma : Fin (pb.A r), IsClosed (V' gamma))
    (hV'sub : forall gamma : Fin (pb.A r), V' gamma ⊆ V gamma)
    (hKV0 :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) := (X.obj (L.φ n)).t2TangentBundle
      forall gamma : Fin (pb.A r), forall v : E,
        v ∈ (NormalCoordinates.normalChartAt (I := I) (X.obj (L.φ n)).metric (x gamma n)) ''
            NetLimitData.hatSourceCage (I := I) (X := X) hd P L pb r n gamma ->
        forall a : Nat, normalTransition (I := I) (X.obj (L.φ a)) (x gamma a) (y gamma a) v ∈ V' gamma) :
    exists phi : Nat -> Nat, StrictMono phi /\
      (let hcomplete := NetLimitData.sourceComplete (I := I) (X := X) hd P L n hX hconn
       letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
       letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
       letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
       letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
       letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
       letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) := (X.obj (L.φ n)).t2TangentBundle
       letI : ConnectedSpace (X.obj (L.φ n)).M := hconn
       letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
         Manifold.metrizableSpace I (X.obj (L.φ n)).M
       letI : T3Space (X.obj (L.φ n)).M := inferInstance
       letI : RiemannianBundle (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
         ⟨(X.obj (L.φ n)).metric.toRiemannianMetric⟩
       letI : IsContinuousRiemannianBundle E (fun x : (X.obj (L.φ n)).M => TangentSpace I x) :=
         ⟨(X.obj (L.φ n)).metric.inner, (X.obj (L.φ n)).metric.contMDiff.continuous, fun _ _ _ => rfl⟩
       letI : MetricSpace (X.obj (L.φ n)).M := HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
       let ptsSeq := NetLimitData.decodedCompPts (I := I) (X.obj (L.φ n)).metric
         (fun gamma => x gamma n)
         (fun gamma a => normalTransition (I := I) (X.obj (L.φ (phi a))) (x gamma (phi a)) (y gamma (phi a)))
         (fun gamma b => normalTransition (I := I) (X.obj (L.φ (phi b))) (y gamma (phi b)) (x gamma (phi b)))
       forall eps : Real, eps > 0 -> exists N : Nat,
         forall a : Nat, a >= N -> forall b : Nat, b >= N ->
           forall xx : (X.obj (L.φ n)).M,
             xx ∈ NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n ->
               dist xx
                 (centerAverageOn (I := I) (X.obj (L.φ n)).metric
                   (NetLimitData.hatSourceBall (I := I) (X := X) hd P L r n)
                   (fun yy : (X.obj (L.φ n)).M => fun gamma : Fin (pb.A r) => rho gamma yy)
                   (centerAverage.activeFill
                     (fun yy : (X.obj (L.φ n)).M => fun gamma : Fin (pb.A r) => rho gamma yy)
                     (ptsSeq a b) (fun yy : (X.obj (L.φ n)).M => yy))
                   join (fun yy : (X.obj (L.φ n)).M => yy)
                   (fun xx => radSeq (phi a) (phi b) xx)
                   (fun yy : (X.obj (L.φ n)).M => yy)
                   (fun yy hy => centerAverage.inputOfFillSelf (I := I)
                     (g := (X.obj (L.φ n)).metric)
                     (μ := fun yy : (X.obj (L.φ n)).M => fun gamma : Fin (pb.A r) => rho gamma yy)
                     (pts := ptsSeq a b) (join := join)
                     (r := fun xx => radSeq (phi a) (phi b) xx) (qstar := fun yy : (X.obj (L.φ n)).M => yy)
                     yy hcomplete (hrad (phi a) (phi b) yy hy) (hactive0 (phi a) (phi b) yy hy)
                     ((NetLimitData.hatPOUDataTwo (I := I) (X := X) (hd := hd)
                       (D := D) (P := P) (L := L) (pb := pb) (r := r) (n := n)
                       (rho := rho) (hrho := hrho) a b hy).1.1)
                     ((NetLimitData.hatPOUDataTwo (I := I) (X := X) (hd := hd)
                       (D := D) (P := P) (L := L) (pb := pb) (r := r) (n := n)
                       (rho := rho) (hrho := hrho) a b hy).1.2.1)
                     (hstrict0 (phi a) (phi b) yy hy)) xx) < eps) := by
  classical
  have htail (gamma : Fin (pb.A r)) : ∀ᶠ k in atTop,
      NormalTransAt (I := I)
        (NormalCoordMetricBoundInput.subseq (I := I) metricInput L.φ)
        x y U V Ua Va gamma k := by
    filter_upwards
      [hUmetric gamma, hVmetric gamma, hUametric gamma, hVametric gamma,
        hUexp gamma, hVexp gamma, hUaexp gamma, hVaexp gamma,
        hJ gamma, hJbar gamma, hovlJ gamma, hovlJbar gamma,
        hmapJ gamma, hmapJbar gamma, hLeft gamma, hRight gamma]
      with k hkUM hkVM hkUaM hkVaM hkUE hkVE hkUaE hkVaE
        hkJ hkJbar hkOvl hkOvlbar hkMap hkMapbar hkLeft hkRight
    exact
      { Umetric := hkUM
        Vmetric := hkVM
        Uametric := hkUaM
        Vametric := hkVaM
        Uexp := hkUE
        Vexp := hkVE
        Uaexp := hkUaE
        Vaexp := hkVaE
        J := hkJ
        Jbar := hkJbar
        ovlJ := hkOvl
        ovlJbar := hkOvlbar
        mapJ := hkMap
        mapJbar := hkMapbar
        left := hkLeft
        right := hkRight }
  obtain ⟨phi, hphi, Jinf, Jbarinf, hspec⟩ :=
    existsTransTail (I := I) (X := X.subseq L.φ)
      (NormalCoordMetricBoundInput.subseq (I := I) metricInput L.φ)
      x y U V Ua Va hU hVopen hUa hVa hUanorm hVanorm htail
  refine ⟨phi, hphi, ?_⟩
  exact stepCJoinFixed hd P L pb r n rho hrho join
    (fun a b => radSeq (phi a) (phi b))
    (fun gamma => x gamma n) U V
    (fun gamma a => normalTransition (I := I) (X.obj (L.φ (phi a))) (x gamma (phi a)) (y gamma (phi a)))
    Jinf
    (fun gamma b => normalTransition (I := I) (X.obj (L.φ (phi b))) (y gamma (phi b)) (x gamma (phi b)))
    Jbarinf
    hconn hX hcenter hgp
    (fun a b => hrad (phi a) (phi b))
    (fun a b => hactive0 (phi a) (phi b))
    (fun a b => hstrict0 (phi a) (phi b))
    hVopen
    (fun gamma => by
      simpa only [PointedRiemannianSeq.subseq] using (hspec gamma).2.2.2.2.1)
    (fun gamma => by
      simpa only [PointedRiemannianSeq.subseq] using (hspec gamma).2.2.2.2.2.1)
    (fun gamma => (hspec gamma).2.2.1)
    (fun gamma => (hspec gamma).2.2.2.1)
    (fun gamma => (hspec gamma).2.2.2.2.2.2.1)
    hKU V' hV'closed hV'sub
    (fun gamma v hv a => hKV0 gamma v hv (phi a))

end HCGCompactness
end DifferentialGeometry
