import DifferentialGeometry.Geometry.Metric.TensorInner.TangentNormDiamond
import DifferentialGeometry.Geometry.Comparison.Volume.Packing
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.BoundedGeometry
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.PointedEmetric
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepAInputs

set_option autoImplicit false
set_option linter.style.longLine false










noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff Bundle

variable {E : Type uE} [NormedAddCommGroup E]
variable [NormedSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]







theorem exists_pairR_of_boundedGeometry
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (hcomplete : MetricComplete (I := I) Y)
    (hconn : letI : TopologicalSpace Y.M := Y.topology; ConnectedSpace Y.M)
    (hgeom : BoundedGeometry (I := I) Y)
    (p : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : IsManifold I 1 Y.M :=
      IsManifold.of_le (I := I) (M := Y.M) (n := ∞)
        (by decide : (1 : WithTop ℕ∞) ≤ ∞)
    letI : SigmaCompactSpace Y.M := Y.sigmaCompact
    letI : T2Space Y.M := Y.t2
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    letI : TopologicalSpace.MetrizableSpace Y.M := Manifold.metrizableSpace I Y.M
    letI : T3Space Y.M := inferInstance
    letI cg : Bundle.ContinuousRiemannianMetric E (TangentSpace I : Y.M → Type _) :=
      Y.metric.toContinuousRiemannianMetric
    letI : Bundle.RiemannianBundle (fun x : Y.M => TangentSpace I x) :=
      ⟨cg.toRiemannianMetric⟩
    letI : EMetricSpace Y.M := EMetricSpace.ofRiemannianMetric I Y.M
    letI : PseudoEMetricSpace Y.M := inferInstance
    letI : ConnectedSpace Y.M := hconn
    letI : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
    ∃ C D Blo A δ : Real, 0 < C ∧ 0 < D ∧ 0 < Blo ∧ 0 < δ ∧
      ∀ {s : Real}, 0 < s → s < δ →
        let Rlo : Real := s / (2 * C)
        let Rup : Real := D * s
        let Bhi : Real :=
          max
            (A + gronwallBound 0
              (max (Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank Real E)) : Real)) *
                hgeom.C 0 * (C * Rup) ^ 2) 1)
              ((Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank Real E)) : Real)) *
                hgeom.C 0 * (C * Rup) ^ 2) * A) 1)
            0
        letI : MetricSpace Y.M :=
          HopfRinow.riemMetricSpace (I := I) (M := Y.M)
        ENNReal.ofReal (Real.sqrt ((Blo ^ 2) ^ Module.finrank Real E)) *
            (ENNReal.ofReal (Rlo ^ Module.finrank Real E) *
              (Integral.Measure.modelHaar (E := E)) (Metric.ball (0 : E) 1)) ≤
          Integral.Measure.riemannianVolumeMeasure (I := I) (M := Y.M) Y.metric
            (Metric.ball p s) ∧
        Integral.Measure.riemannianVolumeMeasure (I := I) (M := Y.M) Y.metric
            (Metric.ball p s) ≤
          ENNReal.ofReal
            (Real.sqrt (((Module.finrank Real E).factorial : Real) *
              (Bhi * Bhi) ^ Module.finrank Real E)) *
            (ENNReal.ofReal (Rup ^ Module.finrank Real E) *
              (Integral.Measure.modelHaar (E := E)) (Metric.ball (0 : E) 1)) := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : IsManifold I 1 Y.M :=
    IsManifold.of_le (I := I) (M := Y.M) (n := ∞)
      (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  letI : SigmaCompactSpace Y.M := Y.sigmaCompact
  letI : T2Space Y.M := Y.t2
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  letI : TopologicalSpace.MetrizableSpace Y.M := Manifold.metrizableSpace I Y.M
  letI : T3Space Y.M := inferInstance
  letI cg : Bundle.ContinuousRiemannianMetric E (TangentSpace I : Y.M → Type _) :=
    Y.metric.toContinuousRiemannianMetric
  letI : Bundle.RiemannianBundle (fun x : Y.M => TangentSpace I x) :=
    ⟨cg.toRiemannianMetric⟩
  letI : EMetricSpace Y.M := EMetricSpace.ofRiemannianMetric I Y.M
  letI : PseudoEMetricSpace Y.M := inferInstance
  letI : ConnectedSpace Y.M := hconn
  letI : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
  have hEnorm := fun x v =>
    (DifferentialGeometry.Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
      (I := I) Y.metric x v)
  obtain ⟨C, D, Blo, A, hC, hD, hBlo, hvol⟩ :=
    DifferentialGeometry.Geometry.Riemannian.VolumeComparison.exists_pairR_bound
      (I := I) (M := Y.M) Y.metric hEnorm p
  obtain ⟨δ, hδ, hsmall⟩ :=
    hvol (Rm := hgeom.C 0) (hgeom.nonneg 0)
      (rm04Bound_of_geom (I := I) hgeom)
  exact ⟨C, D, Blo, A, δ, hC, hD, hBlo, hδ, hsmall⟩







theorem exists_pairR_of_seqBoundedGeometry
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k : Nat,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (hgeom : SeqBoundedGeometry (I := I) X)
    (k : Nat) (p : (X.obj k).M) :
    let Y := X.obj k
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : IsManifold I 1 Y.M :=
      IsManifold.of_le (I := I) (M := Y.M) (n := ∞)
        (by decide : (1 : WithTop ℕ∞) ≤ ∞)
    letI : SigmaCompactSpace Y.M := Y.sigmaCompact
    letI : T2Space Y.M := Y.t2
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    letI : TopologicalSpace.MetrizableSpace Y.M := Manifold.metrizableSpace I Y.M
    letI : T3Space Y.M := inferInstance
    letI cg : Bundle.ContinuousRiemannianMetric E (TangentSpace I : Y.M → Type _) :=
      Y.metric.toContinuousRiemannianMetric
    letI : Bundle.RiemannianBundle (fun x : Y.M => TangentSpace I x) :=
      ⟨cg.toRiemannianMetric⟩
    letI : EMetricSpace Y.M := EMetricSpace.ofRiemannianMetric I Y.M
    letI : PseudoEMetricSpace Y.M := inferInstance
    letI : ConnectedSpace Y.M := hconn k
    letI : CompleteSpace Y.M := MetricComplete.complete (I := I) Y (hcomplete.complete k)
    ∃ C D Blo A δ : Real, 0 < C ∧ 0 < D ∧ 0 < Blo ∧ 0 < δ ∧
      ∀ {s : Real}, 0 < s → s < δ →
        let Rlo : Real := s / (2 * C)
        let Rup : Real := D * s
        let Bhi : Real :=
          max
            (A + gronwallBound 0
              (max (Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank Real E)) : Real)) *
                hgeom.C 0 * (C * Rup) ^ 2) 1)
              ((Real.sqrt ((Fintype.card (Fin 1 -> Fin (Module.finrank Real E)) : Real)) *
                hgeom.C 0 * (C * Rup) ^ 2) * A) 1)
            0
        letI : MetricSpace Y.M :=
          HopfRinow.riemMetricSpace (I := I) (M := Y.M)
        ENNReal.ofReal (Real.sqrt ((Blo ^ 2) ^ Module.finrank Real E)) *
            (ENNReal.ofReal (Rlo ^ Module.finrank Real E) *
              (Integral.Measure.modelHaar (E := E)) (Metric.ball (0 : E) 1)) ≤
          Integral.Measure.riemannianVolumeMeasure (I := I) (M := Y.M) Y.metric
            (Metric.ball p s) ∧
        Integral.Measure.riemannianVolumeMeasure (I := I) (M := Y.M) Y.metric
            (Metric.ball p s) ≤
          ENNReal.ofReal
            (Real.sqrt (((Module.finrank Real E).factorial : Real) *
              (Bhi * Bhi) ^ Module.finrank Real E)) *
            (ENNReal.ofReal (Rup ^ Module.finrank Real E) *
              (Integral.Measure.modelHaar (E := E)) (Metric.ball (0 : E) 1)) := by
  let Y := X.obj k
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : IsManifold I 1 Y.M :=
    IsManifold.of_le (I := I) (M := Y.M) (n := ∞)
      (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  letI : SigmaCompactSpace Y.M := Y.sigmaCompact
  letI : T2Space Y.M := Y.t2
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  letI : TopologicalSpace.MetrizableSpace Y.M := Manifold.metrizableSpace I Y.M
  letI : T3Space Y.M := inferInstance
  letI cg : Bundle.ContinuousRiemannianMetric E (TangentSpace I : Y.M → Type _) :=
    Y.metric.toContinuousRiemannianMetric
  letI : Bundle.RiemannianBundle (fun x : Y.M => TangentSpace I x) :=
    ⟨cg.toRiemannianMetric⟩
  letI : EMetricSpace Y.M := EMetricSpace.ofRiemannianMetric I Y.M
  letI : PseudoEMetricSpace Y.M := inferInstance
  letI : ConnectedSpace Y.M := hconn k
  letI : CompleteSpace Y.M := MetricComplete.complete (I := I) Y (hcomplete.complete k)
  let hgeom_k : BoundedGeometry (I := I) Y := {
    C := hgeom.C
    nonneg := hgeom.nonneg
    bound := hgeom.bound k }
  obtain ⟨C0, D, Blo, A, δ, hC0, hD, hBlo, hδ, hsmall⟩ :=
    exists_pairR_of_boundedGeometry (I := I) Y (hcomplete.complete k) (hconn k) hgeom_k p
  refine ⟨C0, D, Blo, A, δ, hC0, hD, hBlo, hδ, ?_⟩
  intro s hs hsd
  simpa [Y, hgeom_k] using hsmall (s := s) hs hsd







structure UniformBallPack
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I)) where

  dist : PointedSeqDistance (I := I) X

  ms : ∀ k : Nat, MetricSpace (X.obj k).M

  dist_eq : ∀ k : Nat, ∀ x y : (X.obj k).M,
    dist k x y =
      (letI : MetricSpace (X.obj k).M := ms k
       @Dist.dist (X.obj k).M _ x y)

  r0 : Real
  r0_pos : 0 < r0

  Imult : Real → Nat

  L : Real → Real → Real

  U : Real → Real → Real
  L_pos : ∀ m r : Real, 0 < r → m * r ≤ r0 → 0 < L m r
  U_nonneg : ∀ m r : Real, 0 < r → m * r ≤ r0 → 0 ≤ U m r
  cap : ∀ m r : Real, 0 < r → m * r ≤ r0 →
    U m r < ((Imult m + 1 : Nat) : Real) * L m r
  small_meas : ∀ m : Real, ∀ k : Nat, ∀ p : (X.obj k).M, ∀ {r : Real},
    0 < r → m * r ≤ r0 →
      let Y := X.obj k
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space Y.M := Y.t2
      letI : SigmaCompactSpace Y.M := Y.sigmaCompact
      letI : MetricSpace Y.M := ms k
      letI : MeasurableSpace Y.M := borel Y.M
      MeasurableSet (Metric.ball p (r / 2))
  lower : ∀ m : Real, ∀ k : Nat, ∀ p : (X.obj k).M, ∀ {r : Real},
    0 < r → m * r ≤ r0 →
      let Y := X.obj k
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space Y.M := Y.t2
      letI : SigmaCompactSpace Y.M := Y.sigmaCompact
      letI : MetricSpace Y.M := ms k
      letI : MeasurableSpace Y.M := borel Y.M
      ENNReal.ofReal (L m r) ≤
        Integral.Measure.riemannianVolumeMeasure (I := I) (M := Y.M) Y.metric
          (Metric.ball p (r / 2))
  upper : ∀ m : Real, ∀ k : Nat, ∀ z : (X.obj k).M, ∀ {r : Real},
    0 < r → m * r ≤ r0 →
      let Y := X.obj k
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space Y.M := Y.t2
      letI : SigmaCompactSpace Y.M := Y.sigmaCompact
      letI : MetricSpace Y.M := ms k
      letI : MeasurableSpace Y.M := borel Y.M
      Integral.Measure.riemannianVolumeMeasure (I := I) (M := Y.M) Y.metric
          (Metric.ball z ((m + 1 / 2) * r)) ≤
        ENNReal.ofReal (U m r)

namespace UniformBallPack







def toVCInput {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (h : UniformBallPack (I := I) X) :
    VolumeComparisonInput (I := I) X where
  dist := h.dist
  r0 := h.r0
  r0_pos := h.r0_pos
  Imult := h.Imult
  ballMult := by
    intro m k α _ _ centers r hr hcap hsep z J hJz
    let Y := X.obj k
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space Y.M := Y.t2
    letI : SigmaCompactSpace Y.M := Y.sigmaCompact
    letI : MetricSpace Y.M := h.ms k
    letI : MeasurableSpace Y.M := borel Y.M
    let μ := Integral.Measure.riemannianVolumeMeasure (I := I) (M := Y.M) Y.metric
    have hsep_metric :
        ∀ i ∈ J, ∀ j ∈ J, i ≠ j →
          r ≤ @Dist.dist Y.M _ (centers i) (centers j) := by
      intro i hi j hj hij
      simpa [h.dist_eq k] using hsep i j hij
    have hJz_metric :
        ∀ j ∈ J, @Dist.dist Y.M _ (centers j) z ≤ m * r := by
      intro j hj
      simpa [h.dist_eq k] using hJz j hj
    exact
      DifferentialGeometry.Geometry.Riemannian.VolumeComparison.ball_card_le_meas
        μ J centers z
        (h.L_pos m r hr hcap)
        (h.U_nonneg m r hr hcap)
        (fun j _hj => h.small_meas m k (centers j) hr hcap)
        hsep_metric hJz_metric
        (fun j _hj => h.lower m k (centers j) hr hcap)
        (h.upper m k z hr hcap)
        (h.cap m r hr hcap)

end UniformBallPack

end HCGCompactness
end DifferentialGeometry
