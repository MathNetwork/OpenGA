import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.RicciFlowConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.HamiltonPositiveRicci

set_option autoImplicit false
set_option linter.style.longLine false











noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold ContDiff
open DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci

variable {E : Type uE} [NormedAddCommGroup E]
variable [InnerProductSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M]




def cghToHam3
    (X : PointedFlowSeq.{u, uE, uH} (I := I))
    (origIndex : Nat -> Nat) (horig : StrictMono origIndex)
    (toOrig : forall i : Nat,
      letI : TopologicalSpace (X.term i).M := (X.term i).topology
      letI : ChartedSpace H (X.term i).M := (X.term i).charted
      (X.term i).M ≃ₘ⟮I, I⟯ M)
    (L : PointedFlowData.{u, uE, uH} (I := I) X.D)
    (subseq : Nat -> Nat) (hsubseq : StrictMono subseq)
    (hconv : SmoothCGHConverges (I := I) X L subseq)
    (hcomplete : forall t : Real, t ∈ X.D.carrier ->
      MetricComplete (I := I) (L.atTime (I := I) t)) :
    Ham3CGHLimitData (I := I) M where
  N := L.M
  topology := L.topology
  charted := L.charted
  smooth := L.smooth
  smooth_plus := by
    letI : TopologicalSpace L.M := L.topology
    letI : ChartedSpace H L.M := L.charted
    letI : IsManifold I ∞ L.M := L.smooth
    change IsManifold I ∞ L.M
    infer_instance
  sigmaCompact := L.sigmaCompact
  t2 := L.t2
  t2TangentBundle := L.t2TangentBundle
  basepoint := L.basepoint
  D := X.D
  S := L.S
  isSolution := L.isSolution
  sourceTerm := X.term
  origIndex := origIndex
  origStrict := horig
  cghSubseq := subseq
  cghStrict := hsubseq
  cgh := hconv
  sourceToOrig := toOrig
  limitComplete := hcomplete



structure Ham3SourceLink
    {g0 : SmoothRiemannianMetric I M}
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (Q : Ham3BlowupData M) (hsel : Ham3PointSel (I := I) P Q)
    (X : PointedFlowSeq.{u, uE, uH} (I := I)) where
  origIndex : Nat -> Nat
  strictMono : StrictMono origIndex
  toOrig : forall i : Nat,
    letI : TopologicalSpace (X.term i).M := (X.term i).topology
    letI : ChartedSpace H (X.term i).M := (X.term i).charted
    (X.term i).M ≃ₘ⟮I, I⟯ M
  time_mem : forall (i : Nat) (t : Real), t ∈ X.D.carrier ->
    t ∈ (DifferentialGeometry.PDE.RicciFlow.paraInterval P.D (Q.time (origIndex i))
      (ham3BlowupScale (I := I) P Q (origIndex i))
      (hsel.1 (origIndex i)) (hsel.2.2.1 (origIndex i))).carrier
  basepoint_map : forall i : Nat,
    letI : TopologicalSpace (X.term i).M := (X.term i).topology
    letI : ChartedSpace H (X.term i).M := (X.term i).charted
    toOrig i (X.term i).basepoint = Q.point (origIndex i)
  metric_eq : forall i : Nat,
    letI : TopologicalSpace (X.term i).M := (X.term i).topology
    letI : ChartedSpace H (X.term i).M := (X.term i).charted
    letI : IsManifold I ∞ (X.term i).M := (X.term i).smooth
    letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) (X.term i).M := by
      change IsManifold I ∞ (X.term i).M
      infer_instance
    letI : SigmaCompactSpace (X.term i).M := (X.term i).sigmaCompact
    letI : T2Space (X.term i).M := (X.term i).t2
    forall t : Real, t ∈ X.D.carrier ->
      (X.term i).S.base.metric t =
        Diffeomorph.pullbackMetricCross
          ((ham3RescaledSol (I := I) P Q hsel (origIndex i)).base.metric t)
          (toOrig i)
  baseScalar : forall i : Nat,
    letI : TopologicalSpace (X.term i).M := (X.term i).topology
    letI : ChartedSpace H (X.term i).M := (X.term i).charted
    letI : IsManifold I ∞ (X.term i).M := (X.term i).smooth
    letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) (X.term i).M := by
      change IsManifold I ∞ (X.term i).M
      infer_instance
    letI : SigmaCompactSpace (X.term i).M := (X.term i).sigmaCompact
    letI : T2Space (X.term i).M := (X.term i).t2
    (X.term i).S.scalar 0 (X.term i).basepoint =
      ham3RescaledScalar (I := I) P Q (origIndex i) 0 (Q.point (origIndex i))



omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem Ham3SourceLink.realizes
    {g0 : SmoothRiemannianMetric I M}
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (Q : Ham3BlowupData M) (hsel : Ham3PointSel (I := I) P Q)
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    (hsource : Ham3SourceLink (I := I) (M := M) P Q hsel X)
    (L : PointedFlowData.{u, uE, uH} (I := I) X.D)
    (subseq : Nat -> Nat) (hsubseq : StrictMono subseq)
    (hconv : SmoothCGHConverges (I := I) X L subseq)
    (hcomplete : forall t : Real, t ∈ X.D.carrier ->
      MetricComplete (I := I) (L.atTime (I := I) t)) :
    Ham3SourceRealizes (I := I) (M := M) P Q hsel
      (cghToHam3 (I := I) (M := M) X hsource.origIndex hsource.strictMono
        hsource.toOrig L subseq hsubseq hconv hcomplete) := by
  refine
    { time_mem := ?_
      basepoint_map := ?_
      metric_eq := ?_ }
  · intro i t ht
    exact hsource.time_mem i t ht
  · intro i
    simpa [cghToHam3] using hsource.basepoint_map i
  · intro i t ht
    simpa [cghToHam3] using hsource.metric_eq i t ht




def HamCGHConclusion
    {g0 : SmoothRiemannianMetric I M}
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (Q : Ham3BlowupData M) (hsel : Ham3PointSel (I := I) P Q)
    (X : PointedFlowSeq.{u, uE, uH} (I := I))
    (hsource : Ham3SourceLink (I := I) (M := M) P Q hsel X) : Prop :=
  exists L : PointedFlowData.{u, uE, uH} (I := I) X.D,
    exists subseq : Nat -> Nat,
    exists hsubseq : StrictMono subseq,
    exists hconv : SmoothCGHConverges (I := I) X L subseq,
    exists hcomplete : forall t : Real, t ∈ X.D.carrier ->
      MetricComplete (I := I) (L.atTime (I := I) t),
      (letI : TopologicalSpace L.M := L.topology
       ConnectedSpace L.M) /\
      (let Lh := cghToHam3 (I := I) (M := M) X hsource.origIndex
        hsource.strictMono hsource.toOrig L subseq hsubseq hconv hcomplete
       Ham3RicNonnegTransfer (I := I) (M := M) P Q hsel Lh /\
         LimitScalarPos (I := I) (M := M) Lh /\
         Ham3PinchTransfer (I := I) (M := M) P Q hsel Lh)






omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem baseScalarConv_of_smoothCGH
    {g0 : SmoothRiemannianMetric I M}
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (Q : Ham3BlowupData M)
    (hsel : Ham3PointSel (I := I) P Q)
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {L : PointedFlowData.{u, uE, uH} (I := I) X.D}
    {subseq : Nat -> Nat}
    (hsource : Ham3SourceLink (I := I) (M := M) P Q hsel X)
    (h0 : (0 : Real) ∈ X.D.carrier)
    (hsubseq : StrictMono subseq)
    (hconv : SmoothCGHConverges (I := I) X L subseq)
    (hcomplete : forall t : Real, t ∈ X.D.carrier ->
      MetricComplete (I := I) (L.atTime (I := I) t)) :
    Ham3LimitBaseScalarConv (I := I) (M := M) P Q
      (cghToHam3 (I := I) (M := M) X hsource.origIndex hsource.strictMono
        hsource.toOrig L subseq hsubseq hconv hcomplete) := by
  classical
  have hscalar := hconv.scalar_converges 0 h0 L.basepoint
  refine hscalar.congr' ?_
  filter_upwards with k
  letI : TopologicalSpace (X.term (subseq k)).M :=
    (X.term (subseq k)).topology
  letI : ChartedSpace H (X.term (subseq k)).M :=
    (X.term (subseq k)).charted
  letI : IsManifold I ∞ (X.term (subseq k)).M :=
    (X.term (subseq k)).smooth
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1)
      (X.term (subseq k)).M := by
    change IsManifold I ∞ (X.term (subseq k)).M
    infer_instance
  letI : SigmaCompactSpace (X.term (subseq k)).M :=
    (X.term (subseq k)).sigmaCompact
  letI : T2Space (X.term (subseq k)).M :=
    (X.term (subseq k)).t2
  calc
    (X.term (subseq k)).S.scalar 0 (hconv.spatial.maps.map k (L.atTime 0).basepoint)
        = (X.term (subseq k)).S.scalar 0 (X.term (subseq k)).basepoint := by
          simp [PointedCGHMaps.map, hconv.spatial.maps.basepoint_map k]
    _ = ham3RescaledScalar (I := I) P Q (hsource.origIndex (subseq k)) 0
        (Q.point (hsource.origIndex (subseq k))) := by
          simpa using hsource.baseScalar (subseq k)



omit [NeZero (Module.finrank ℝ E)] in
theorem toHam3Exists
    {g0 : SmoothRiemannianMetric I M}
    (P : Ham3FlowPackage (I := I) (M := M) g0)
    (Q : Ham3BlowupData M)
    (hsel : Ham3PointSel (I := I) P Q)
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    (hwindow : Set.Icc (-(ham3_r0 ^ 2)) 0 ⊆ X.D.carrier)
    (hreg : Set.Ioo (-(ham3_r0 ^ 2)) 0 ⊆ X.D.regular)
    (hsource : Ham3SourceLink (I := I) (M := M) P Q hsel X)
    (hcompact : HamCGHConclusion (I := I) (M := M) P Q hsel X hsource) :
    Ham3CGHLimitExists (I := I) P Q hsel := by
  rcases hcompact with
    ⟨L, subseq, hsubseq, hconv, hcomplete, hconnected, htransfers⟩
  let Lh : Ham3CGHLimitData (I := I) M :=
    cghToHam3 (I := I) (M := M) X hsource.origIndex hsource.strictMono
      hsource.toOrig L subseq hsubseq hconv hcomplete
  change Ham3RicNonnegTransfer (I := I) (M := M) P Q hsel Lh /\
    LimitScalarPos (I := I) (M := M) Lh /\
    Ham3PinchTransfer (I := I) (M := M) P Q hsel Lh at htransfers
  rcases htransfers with ⟨hricTransfer, hscalarPos, hpinchTransfer⟩
  have hreal : Ham3SourceRealizes (I := I) (M := M) P Q hsel Lh :=
    Ham3SourceLink.realizes (I := I) (M := M) P Q hsel hsource L subseq
      hsubseq hconv hcomplete
  have hconnHam :
      Ham3LimitConnected (I := I) (M := M) Lh := by
    simpa [Lh, DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.Ham3LimitConnected,
      cghToHam3] using
      hconnected
  have hbdHam :
      Ham3LimitBoundaryless (I := I) (M := M) Lh := by
    simpa [Lh, DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.Ham3LimitBoundaryless,
      cghToHam3] using (inferInstance : I.Boundaryless)
  refine
    ⟨Lh, hreal, Lh.subseq_strict,
      hwindow, hreg, hconnHam, hbdHam, ?_,
      hricTransfer,
      baseScalarConv_of_smoothCGH (I := I) (M := M) P Q hsel hsource
        (hwindow (Set.mem_Icc.mpr ⟨neg_nonpos.mpr (sq_nonneg ham3_r0), le_refl 0⟩))
        hsubseq hconv hcomplete,
      ⟨hscalarPos, hpinchTransfer⟩⟩
  simpa [Lh, DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.Ham3LimitFlow,
    cghToHam3] using
    L.isSolution

end HCGCompactness
end DifferentialGeometry
