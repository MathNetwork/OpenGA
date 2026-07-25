import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.ConvFieldInputs
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.FlowLimitBuild
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.FlowLimitUpgrade
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricCompactnessSubseq







set_option autoImplicit false
set_option linter.style.longLine false
set_option backward.isDefEq.respectTransparency false













noncomputable section

open Set Function Filter Bundle Manifold Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.RicciFlow (SolutionOn IsSolutionOn)

namespace DifferentialGeometry
namespace HCGCompactness

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]








def PointedCGHMaps.compSubseq
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X P subseq)
    (φ : Nat -> Nat) (hφ : StrictMono φ) :
    PointedCGHMaps (I := I) X P (subseq ∘ φ) where
  partialDiffeomorph k := Φ.partialDiffeomorph (φ k)
  source_exhausts := by
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    exact Φ.source_exhausts.comp_subseq hφ
  base_mem k := Φ.base_mem (φ k)
  basepoint_map k := Φ.basepoint_map (φ k)

section Endgame

variable {X : PointedFlowSeq (I := I)}












noncomputable def endgamePhi
    (mc : MetricCompactnessConclusion (I := I) (X.atZero (I := I)))
    (L : PointedFlowData (I := I) X.D)
    (hL0 : L.atTime (I := I) 0 = mc.limit) :
    PointedCGHMaps (I := I) X (L.atTime 0) mc.subseq :=
  pointedCGHMaps_of_atZero (I := I) X L mc.subseq (hL0.symm ▸ mc.maps)














noncomputable def flowUpgrade_of_maps
    (mc : MetricCompactnessConclusion (I := I) (X.atZero (I := I)))
    (L : PointedFlowData (I := I) X.D)
    (P : PointedRiemannianManifold (I := I))
    (hPlim : P = mc.limit)
    (hPL : L.atTime (I := I) 0 = P)
    (Φ : PointedCGHMaps (I := I) X P mc.subseq)
    (R :
      letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M)
    (bf : BumpFamily (I := I) Φ)
    (hsrc : SrcSigma (I := I) Φ)
    (htgt : TgtSigma (I := I) Φ)
    (β ψ : Real)
    (hcarrier : X.D.carrier ⊆ Set.Icc β ψ)
    (co : ConvOut (I := I) Φ R bf hsrc htgt β ψ)
    (hLmetric :
      letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      letI : T2Space L.M := L.t2
      letI : IsManifold I ∞ L.M := L.smooth
      letI : SigmaCompactSpace L.M := L.sigmaCompact
      forall t : Real, t ∈ Set.Icc β ψ ->
        HEq (L.S.family.metric t) (co.gInf t))
    (scalar : ScalarPullbackTendsto (I := I)
      (hPL.symm ▸ (Φ.compSubseq co.φ co.hφ) :
        PointedCGHMaps (I := I) X (L.atTime 0) (mc.subseq ∘ co.φ))) :
    FlowUpgradeData (I := I) X mc := by
  have hL0 : L.atTime (I := I) 0 = mc.limit := hPL.trans hPlim
  subst hPL
  letI : TopologicalSpace L.M := L.topology
  letI : ChartedSpace H L.M := L.charted
  letI : T2Space L.M := L.t2
  letI : IsManifold I ∞ L.M := L.smooth
  letI : SigmaCompactSpace L.M := L.sigmaCompact
  letI : TopologicalSpace (L.atTime 0).M := L.topology
  letI : ChartedSpace H (L.atTime 0).M := L.charted
  letI : T2Space (L.atTime 0).M := L.t2
  letI : IsManifold I ∞ (L.atTime 0).M := L.smooth
  letI : SigmaCompactSpace (L.atTime 0).M := L.sigmaCompact
  have hLm : forall t : Real, t ∈ Set.Icc β ψ -> L.S.family.metric t = co.gInf t :=
    fun t ht => eq_of_heq (hLmetric t ht)
  have hscalar : ScalarPullbackTendsto (I := I) (Φ.compSubseq co.φ co.hφ) := scalar

  set mc' := mc.compSubseq co.φ co.hφ with hmc'
  set Φ' := (Φ).compSubseq co.φ co.hφ with hΦ'

  refine ⟨co.φ, co.hφ, ?_⟩
  change FlowLimitData (I := I) X mc'
  refine
    { L := L
      hL0 := by simpa [mc'] using hL0
      maps := Φ'
      scalar := hscalar
      hσsrc := ?_
      hσtgt := ?_
      refMetric := ?_
      conv := ?_ }
  ·
    intro k
    exact Geometry.isSigmaCompact_of_isOpen I (PointedCGHMaps.source_open (I := I) Φ' k)
  ·
    intro k
    letI : TopologicalSpace (X.term (mc'.subseq k)).M := (X.term (mc'.subseq k)).topology
    letI : ChartedSpace H (X.term (mc'.subseq k)).M := (X.term (mc'.subseq k)).charted
    letI : SigmaCompactSpace (X.term (mc'.subseq k)).M := (X.term (mc'.subseq k)).sigmaCompact
    exact Geometry.isSigmaCompact_of_isOpen I (PointedCGHMaps.target_open (I := I) Φ' k)
  ·
    intro k
    exact fun _ => refRes (I := I) Φ' R
      (fun j => Geometry.isSigmaCompact_of_isOpen I
        (PointedCGHMaps.source_open (I := I) Φ' j)) k
  ·


    intro K hK p a b hab ε hε
    have hbridge := ofRP_supOn_conv (I := I) (Φ) R bf hsrc htgt β ψ
      co (letI : TopologicalSpace L.M := L.topology; letI : ChartedSpace H L.M := L.charted; letI : IsManifold I ∞ L.M := L.smooth; letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) L.M := (by change IsManifold I ∞ L.M; infer_instance); letI : SigmaCompactSpace L.M := L.sigmaCompact; letI : T2Space L.M := L.t2; L.S.family.metric) hLm K hK p ε hε
    obtain ⟨k0, hk0⟩ := hbridge
    refine ⟨k0, fun k hk t ht => ?_⟩
    have htβψ : t ∈ Set.Icc β ψ := hcarrier (hab ht)
    exact hk0 k hk t htβψ



omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem flowLimit_of_maps
    (mc : MetricCompactnessConclusion (I := I) (X.atZero (I := I)))
    (L : PointedFlowData (I := I) X.D)
    (P : PointedRiemannianManifold (I := I))
    (hPlim : P = mc.limit)
    (hPL : L.atTime (I := I) 0 = P)
    (Φ : PointedCGHMaps (I := I) X P mc.subseq)
    (R :
      letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M)
    (bf : BumpFamily (I := I) Φ)
    (hsrc : SrcSigma (I := I) Φ)
    (htgt : TgtSigma (I := I) Φ)
    (β ψ : Real)
    (hcarrier : X.D.carrier ⊆ Set.Icc β ψ)
    (co : ConvOut (I := I) Φ R bf hsrc htgt β ψ)
    (hLmetric :
      letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      letI : T2Space L.M := L.t2
      letI : IsManifold I ∞ L.M := L.smooth
      letI : SigmaCompactSpace L.M := L.sigmaCompact
      forall t : Real, t ∈ Set.Icc β ψ ->
        HEq (L.S.family.metric t) (co.gInf t))
    (scalar : ScalarPullbackTendsto (I := I)
      (hPL.symm ▸ (Φ.compSubseq co.φ co.hφ) :
        PointedCGHMaps (I := I) X (L.atTime 0) (mc.subseq ∘ co.φ))) :
    CompactnessConclusion (I := I) X :=
  (flowUpgrade_of_maps (I := I) (X := X) mc L P hPlim hPL Φ R bf hsrc htgt
    β ψ hcarrier co hLmetric scalar).toConclusion



omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem flowLimit_of_co
    (mc : MetricCompactnessConclusion (I := I) (X.atZero (I := I)))
    (L : PointedFlowData (I := I) X.D)
    (hL0 : L.atTime (I := I) 0 = mc.limit)
    (R :
      letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      letI : IsManifold I ∞ L.M := L.smooth
      SmoothRiemannianMetric I L.M)
    (bf : BumpFamily (I := I) (endgamePhi (I := I) mc L hL0))
    (hsrc : SrcSigma (I := I) (endgamePhi (I := I) mc L hL0))
    (htgt : TgtSigma (I := I) (endgamePhi (I := I) mc L hL0))
    (β ψ : Real)
    (hcarrier : X.D.carrier ⊆ Set.Icc β ψ)
    (co : ConvOut (I := I) (endgamePhi (I := I) mc L hL0) R bf hsrc htgt β ψ)
    (hLmetric :
      letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      letI : T2Space L.M := L.t2
      letI : IsManifold I ∞ L.M := L.smooth
      letI : SigmaCompactSpace L.M := L.sigmaCompact
      forall t : Real, t ∈ Set.Icc β ψ -> L.S.family.metric t = co.gInf t)
    (scalar : ScalarPullbackTendsto (I := I)
      ((endgamePhi (I := I) mc L hL0).compSubseq co.φ co.hφ)) :
    CompactnessConclusion (I := I) X :=
  flowLimit_of_maps (I := I) mc L (L.atTime 0) hL0 rfl (endgamePhi (I := I) mc L hL0) R bf hsrc htgt β ψ
    hcarrier co (fun t ht => heq_of_eq (hLmetric t ht)) scalar

















noncomputable def flowUpgrade_of_mc
    (mc : MetricCompactnessConclusion (I := I) (X.atZero (I := I)))
    (Φ₀ : PointedCGHMaps (I := I) X mc.limit mc.subseq)
    (R :
      letI : TopologicalSpace mc.limit.M := mc.limit.topology
      letI : ChartedSpace H mc.limit.M := mc.limit.charted
      letI : IsManifold I ∞ mc.limit.M := mc.limit.smooth
      SmoothRiemannianMetric I mc.limit.M)
    (bf : BumpFamily (I := I) Φ₀)
    (hsrc : SrcSigma (I := I) Φ₀)
    (htgt : TgtSigma (I := I) Φ₀)
    (β ψ : Real)
    (hcarrier : X.D.carrier ⊆ Set.Icc β ψ)
    (co : ConvOut (I := I) Φ₀ R bf hsrc htgt β ψ)
    (hzero :
      letI : TopologicalSpace mc.limit.M := mc.limit.topology
      letI : ChartedSpace H mc.limit.M := mc.limit.charted
      letI : IsManifold I ∞ mc.limit.M := mc.limit.smooth
      co.gInf 0 = mc.limit.metric)
    (hsol :
      letI : TopologicalSpace mc.limit.M := mc.limit.topology
      letI : ChartedSpace H mc.limit.M := mc.limit.charted
      letI : IsManifold I ∞ mc.limit.M := mc.limit.smooth
      letI : SigmaCompactSpace mc.limit.M := mc.limit.sigmaCompact
      letI : T2Space mc.limit.M := mc.limit.t2
      letI : IsManifold I 1 mc.limit.M :=
        IsManifold.of_le (I := I) (M := mc.limit.M) (n := ∞)
          (by decide : (1 : WithTop ℕ∞) ≤ ∞)
      letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) mc.limit.M := by
        change IsManifold I ∞ mc.limit.M
        infer_instance
      DifferentialGeometry.PDE.RicciFlow.IsSolutionOn (I := I)
        ({ base := { metric := co.gInf } } :
          DifferentialGeometry.PDE.RicciFlow.SolutionOn (I := I) (M := mc.limit.M) X.D))
    (scalar : ScalarPullbackTendsto (I := I)
      ((flowOfMetric_atTime (I := I) X.D mc.limit co.gInf hsol 0 hzero).symm ▸
        (Φ₀.compSubseq co.φ co.hφ) :
        PointedCGHMaps (I := I) X
          ((flowOfMetric (I := I) X.D mc.limit co.gInf hsol).atTime 0)
          (mc.subseq ∘ co.φ))) :
    FlowUpgradeData (I := I) X mc := by
  have hL0 :
      (flowOfMetric (I := I) X.D mc.limit co.gInf hsol).atTime (I := I) 0 = mc.limit :=
    flowOfMetric_atTime (I := I) X.D mc.limit co.gInf hsol 0 hzero
  exact flowUpgrade_of_maps (I := I) mc
    (flowOfMetric (I := I) X.D mc.limit co.gInf hsol) mc.limit rfl hL0 Φ₀
    R bf hsrc htgt β ψ hcarrier co (fun t _ => HEq.rfl) scalar



omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem flowLimit_of_mc
    (mc : MetricCompactnessConclusion (I := I) (X.atZero (I := I)))
    (Φ₀ : PointedCGHMaps (I := I) X mc.limit mc.subseq)
    (R :
      letI : TopologicalSpace mc.limit.M := mc.limit.topology
      letI : ChartedSpace H mc.limit.M := mc.limit.charted
      letI : IsManifold I ∞ mc.limit.M := mc.limit.smooth
      SmoothRiemannianMetric I mc.limit.M)
    (bf : BumpFamily (I := I) Φ₀)
    (hsrc : SrcSigma (I := I) Φ₀)
    (htgt : TgtSigma (I := I) Φ₀)
    (β ψ : Real)
    (hcarrier : X.D.carrier ⊆ Set.Icc β ψ)
    (co : ConvOut (I := I) Φ₀ R bf hsrc htgt β ψ)
    (hzero :
      letI : TopologicalSpace mc.limit.M := mc.limit.topology
      letI : ChartedSpace H mc.limit.M := mc.limit.charted
      letI : IsManifold I ∞ mc.limit.M := mc.limit.smooth
      co.gInf 0 = mc.limit.metric)
    (hsol :
      letI : TopologicalSpace mc.limit.M := mc.limit.topology
      letI : ChartedSpace H mc.limit.M := mc.limit.charted
      letI : IsManifold I ∞ mc.limit.M := mc.limit.smooth
      letI : SigmaCompactSpace mc.limit.M := mc.limit.sigmaCompact
      letI : T2Space mc.limit.M := mc.limit.t2
      letI : IsManifold I 1 mc.limit.M :=
        IsManifold.of_le (I := I) (M := mc.limit.M) (n := ∞)
          (by decide : (1 : WithTop ℕ∞) ≤ ∞)
      letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) mc.limit.M := by
        change IsManifold I ∞ mc.limit.M
        infer_instance
      DifferentialGeometry.PDE.RicciFlow.IsSolutionOn (I := I)
        ({ base := { metric := co.gInf } } :
          DifferentialGeometry.PDE.RicciFlow.SolutionOn (I := I) (M := mc.limit.M) X.D))
    (scalar : ScalarPullbackTendsto (I := I)
      ((flowOfMetric_atTime (I := I) X.D mc.limit co.gInf hsol 0 hzero).symm ▸
        (Φ₀.compSubseq co.φ co.hφ) :
        PointedCGHMaps (I := I) X
          ((flowOfMetric (I := I) X.D mc.limit co.gInf hsol).atTime 0)
          (mc.subseq ∘ co.φ))) :
    CompactnessConclusion (I := I) X :=
  (flowUpgrade_of_mc (I := I) (X := X) mc Φ₀ R bf hsrc htgt β ψ
    hcarrier co hzero hsol scalar).toConclusion








noncomputable def endgameCo
    {P : PointedRiemannianManifold (I := I)} {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X P subseq)
    (R : letI : TopologicalSpace P.M := P.topology;
      letI : ChartedSpace H P.M := P.charted; letI : IsManifold I ∞ P.M := P.smooth;
      SmoothRiemannianMetric I P.M)
    (bf : BumpFamily (I := I) Φ) (hsrc : SrcSigma Φ) (htgt : TgtSigma Φ)
    (β ψ : Real) (hβψ : β <= ψ) (hwin : Set.Icc β ψ ⊆ X.D.regular)
    (gRefT : forall k : Nat,
      letI : TopologicalSpace (X.term (subseq k)).M := (X.term (subseq k)).topology
      letI : ChartedSpace H (X.term (subseq k)).M := (X.term (subseq k)).charted
      letI : IsManifold I ∞ (X.term (subseq k)).M := (X.term (subseq k)).smooth
      SmoothRiemannianMetric I ((X.term (subseq k)).M))
    (B : Real -> Real) (Crel Bmax : Real)
    (hBmax : forall t : Real, t ∈ Set.Icc β ψ -> B t <= Bmax)
    (hCrel1 : 1 <= Crel) (hBmax1 : 1 <= Bmax)
    (hequivT : forall k : Nat,
      letI : TopologicalSpace (X.term (subseq k)).M := (X.term (subseq k)).topology
      letI : ChartedSpace H (X.term (subseq k)).M := (X.term (subseq k)).charted
      letI : T2Space (X.term (subseq k)).M := (X.term (subseq k)).t2
      letI : IsManifold I ∞ (X.term (subseq k)).M := (X.term (subseq k)).smooth
      letI : SigmaCompactSpace (X.term (subseq k)).M := (X.term (subseq k)).sigmaCompact
      MetricUniformEquivalentOnWindow (I := I) (Φ.target k) β ψ (gRefT k)
        (fun _ t => (X.term (subseq k)).S.family.metric t) B)
    (hrel : forall k : Nat,
      letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
      letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
      letI : T2Space (SourceDomain (I := I) Φ k) := sourceDomT2 (I := I) Φ k
      letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
      MetricUniformEquivalentOn (I := I)
        (Set.univ : Set (SourceDomain (I := I) Φ k))
        (refRes (I := I) Φ R hsrc k)
        (tgtRefSrc (I := I) Φ gRefT hsrc htgt k) Crel)
    (hShiT : forall N : Nat, exists KShi : Real, 0 <= KShi /\
      forall k : Nat,
        letI : TopologicalSpace (X.term (subseq k)).M := (X.term (subseq k)).topology
        letI : ChartedSpace H (X.term (subseq k)).M := (X.term (subseq k)).charted
        letI : T2Space (X.term (subseq k)).M := (X.term (subseq k)).t2
        letI : IsManifold I ∞ (X.term (subseq k)).M := (X.term (subseq k)).smooth
        letI : SigmaCompactSpace (X.term (subseq k)).M := (X.term (subseq k)).sigmaCompact
        MovingShiBoundOn (I := I) (Φ.target k) β ψ
          (fun _ t => (X.term (subseq k)).S.family.metric t) N KShi)
    (hcovSrc : letI : TopologicalSpace P.M := P.topology;
        letI : ChartedSpace H P.M := P.charted; letI : T2Space P.M := P.t2;
        letI : IsManifold I ∞ P.M := P.smooth; letI : SigmaCompactSpace P.M := P.sigmaCompact;
      forall j : Nat, exists Cs : Real, 0 <= Cs /\
        forall (k : Nat) (t : Real), t ∈ Set.Icc β ψ ->
          forall y : SourceDomain (I := I) Φ k, (y : P.M) ∈ tsupport (bf.chi k) ->
            letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
            letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
            letI : T2Space (SourceDomain (I := I) Φ k) := sourceDomT2 (I := I) Φ k
            letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
            letI : SigmaCompactSpace (SourceDomain (I := I) Φ k) :=
              sourceDomSigmaOf (I := I) Φ k (hsrc k)
            metricCovDerivNorm (I := I) j (srcMetric (I := I) Φ hsrc htgt k t)
              (refRes (I := I) Φ R hsrc k) y <= Cs)
    (hchi : letI : TopologicalSpace P.M := P.topology;
        letI : ChartedSpace H P.M := P.charted; letI : T2Space P.M := P.t2;
        letI : IsManifold I ∞ P.M := P.smooth; letI : SigmaCompactSpace P.M := P.sigmaCompact;
      forall c : Nat, exists Cc : Real, 0 <= Cc /\
        forall (k : Nat) (y : SourceDomain (I := I) Φ k),
          letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
          letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
          letI : T2Space (SourceDomain (I := I) Φ k) := sourceDomT2 (I := I) Φ k
          letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
          letI : SigmaCompactSpace (SourceDomain (I := I) Φ k) :=
            sourceDomSigmaOf (I := I) Φ k (hsrc k)
          Real.sqrt (Tensor0SBundle.normSq0S (I := I)
            (refRes (I := I) Φ R hsrc k) y (0 + c)
            (iterCov (I := I) (refRes (I := I) Φ R hsrc k) 0
              (Tensor0SField.fromScalarField (𝕜 := Real) (E := E) (H := H) (I := I)
                (M := SourceDomain (I := I) Φ k) (∞ : WithTop ℕ∞)
                (chiRes (I := I) Φ bf k) (chiRes_smooth (I := I) Φ bf k)) c y)) <= Cc)
    (hlipG : letI : TopologicalSpace P.M := P.topology;
        letI : ChartedSpace H P.M := P.charted; letI : T2Space P.M := P.t2;
        letI : IsManifold I ∞ P.M := P.smooth; letI : SigmaCompactSpace P.M := P.sigmaCompact;
      forall p : Nat, exists Lt : Real, 0 <= Lt /\
        forall (k : Nat) (s t : Real), s ∈ Set.Icc β ψ -> t ∈ Set.Icc β ψ ->
          forall a : Nat, a <= p ->
            forall y : SourceDomain (I := I) Φ k, (y : P.M) ∈ bf.grow k ->
              letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
              letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
              letI : T2Space (SourceDomain (I := I) Φ k) := sourceDomT2 (I := I) Φ k
              letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
              letI : SigmaCompactSpace (SourceDomain (I := I) Φ k) :=
                sourceDomSigmaOf (I := I) Φ k (hsrc k)
              metricDerivNorm (I := I) a (srcMetric (I := I) Φ hsrc htgt k s)
                (srcMetric (I := I) Φ hsrc htgt k t)
                (refRes (I := I) Φ R hsrc k) y <= Lt * |s - t|) :
    ConvOut (I := I) Φ R bf hsrc htgt β ψ :=
  convOut (I := I) (Φ := Φ) R bf hsrc htgt β ψ hβψ ((Crel * Bmax)⁻¹)
    (inv_pos.2 (mul_pos (lt_of_lt_of_le one_pos hCrel1) (lt_of_lt_of_le one_pos hBmax1)))
    (hbound_of_equiv (I := I) (Φ := Φ) R hsrc htgt β ψ gRefT B Crel Bmax hBmax hCrel1 hequivT hrel)
    (covTail_of_bounds (I := I) (Φ := Φ) R bf hsrc htgt β ψ gRefT B Crel Bmax hBmax hCrel1
      hequivT hrel hcovSrc hchi)
    (lipTail_of_src (I := I) (Φ := Φ) R bf hsrc htgt β ψ hlipG)
    (lipSrc_of_soln (I := I) (Φ := Φ) R hsrc htgt β ψ hβψ hwin gRefT B Crel Bmax hBmax hCrel1
      hBmax1 hequivT hrel hShiT)




omit [NeZero (Module.finrank ℝ E)] in
theorem endgameCo_zero
    {P : PointedRiemannianManifold (I := I)} {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X P subseq)
    (R : letI : TopologicalSpace P.M := P.topology;
      letI : ChartedSpace H P.M := P.charted; letI : IsManifold I ∞ P.M := P.smooth;
      SmoothRiemannianMetric I P.M)
    (bf : BumpFamily (I := I) Φ) (hsrc : SrcSigma Φ) (htgt : TgtSigma Φ)
    (β ψ : Real) (hβψ : β <= ψ) (hwin : Set.Icc β ψ ⊆ X.D.regular)
    (gRefT : forall k : Nat,
      letI : TopologicalSpace (X.term (subseq k)).M := (X.term (subseq k)).topology
      letI : ChartedSpace H (X.term (subseq k)).M := (X.term (subseq k)).charted
      letI : IsManifold I ∞ (X.term (subseq k)).M := (X.term (subseq k)).smooth
      SmoothRiemannianMetric I ((X.term (subseq k)).M))
    (B : Real -> Real) (Crel Bmax : Real)
    (hBmax : forall t : Real, t ∈ Set.Icc β ψ -> B t <= Bmax)
    (hCrel1 : 1 <= Crel) (hBmax1 : 1 <= Bmax)
    (hequivT : forall k : Nat,
      letI : TopologicalSpace (X.term (subseq k)).M := (X.term (subseq k)).topology
      letI : ChartedSpace H (X.term (subseq k)).M := (X.term (subseq k)).charted
      letI : T2Space (X.term (subseq k)).M := (X.term (subseq k)).t2
      letI : IsManifold I ∞ (X.term (subseq k)).M := (X.term (subseq k)).smooth
      letI : SigmaCompactSpace (X.term (subseq k)).M := (X.term (subseq k)).sigmaCompact
      MetricUniformEquivalentOnWindow (I := I) (Φ.target k) β ψ (gRefT k)
        (fun _ t => (X.term (subseq k)).S.family.metric t) B)
    (hrel : forall k : Nat,
      letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
      letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
      letI : T2Space (SourceDomain (I := I) Φ k) := sourceDomT2 (I := I) Φ k
      letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
      MetricUniformEquivalentOn (I := I)
        (Set.univ : Set (SourceDomain (I := I) Φ k))
        (refRes (I := I) Φ R hsrc k)
        (tgtRefSrc (I := I) Φ gRefT hsrc htgt k) Crel)
    (hShiT : forall N : Nat, exists KShi : Real, 0 <= KShi /\
      forall k : Nat,
        letI : TopologicalSpace (X.term (subseq k)).M := (X.term (subseq k)).topology
        letI : ChartedSpace H (X.term (subseq k)).M := (X.term (subseq k)).charted
        letI : T2Space (X.term (subseq k)).M := (X.term (subseq k)).t2
        letI : IsManifold I ∞ (X.term (subseq k)).M := (X.term (subseq k)).smooth
        letI : SigmaCompactSpace (X.term (subseq k)).M := (X.term (subseq k)).sigmaCompact
        MovingShiBoundOn (I := I) (Φ.target k) β ψ
          (fun _ t => (X.term (subseq k)).S.family.metric t) N KShi)
    (hcovSrc : letI : TopologicalSpace P.M := P.topology;
        letI : ChartedSpace H P.M := P.charted; letI : T2Space P.M := P.t2;
        letI : IsManifold I ∞ P.M := P.smooth; letI : SigmaCompactSpace P.M := P.sigmaCompact;
      forall j : Nat, exists Cs : Real, 0 <= Cs /\
        forall (k : Nat) (t : Real), t ∈ Set.Icc β ψ ->
          forall y : SourceDomain (I := I) Φ k, (y : P.M) ∈ tsupport (bf.chi k) ->
            letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
            letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
            letI : T2Space (SourceDomain (I := I) Φ k) := sourceDomT2 (I := I) Φ k
            letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
            letI : SigmaCompactSpace (SourceDomain (I := I) Φ k) :=
              sourceDomSigmaOf (I := I) Φ k (hsrc k)
            metricCovDerivNorm (I := I) j (srcMetric (I := I) Φ hsrc htgt k t)
              (refRes (I := I) Φ R hsrc k) y <= Cs)
    (hchi : letI : TopologicalSpace P.M := P.topology;
        letI : ChartedSpace H P.M := P.charted; letI : T2Space P.M := P.t2;
        letI : IsManifold I ∞ P.M := P.smooth; letI : SigmaCompactSpace P.M := P.sigmaCompact;
      forall c : Nat, exists Cc : Real, 0 <= Cc /\
        forall (k : Nat) (y : SourceDomain (I := I) Φ k),
          letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
          letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
          letI : T2Space (SourceDomain (I := I) Φ k) := sourceDomT2 (I := I) Φ k
          letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
          letI : SigmaCompactSpace (SourceDomain (I := I) Φ k) :=
            sourceDomSigmaOf (I := I) Φ k (hsrc k)
          Real.sqrt (Tensor0SBundle.normSq0S (I := I)
            (refRes (I := I) Φ R hsrc k) y (0 + c)
            (iterCov (I := I) (refRes (I := I) Φ R hsrc k) 0
              (Tensor0SField.fromScalarField (𝕜 := Real) (E := E) (H := H) (I := I)
                (M := SourceDomain (I := I) Φ k) (∞ : WithTop ℕ∞)
                (chiRes (I := I) Φ bf k) (chiRes_smooth (I := I) Φ bf k)) c y)) <= Cc)
    (hlipG : letI : TopologicalSpace P.M := P.topology;
        letI : ChartedSpace H P.M := P.charted; letI : T2Space P.M := P.t2;
        letI : IsManifold I ∞ P.M := P.smooth; letI : SigmaCompactSpace P.M := P.sigmaCompact;
      forall p : Nat, exists Lt : Real, 0 <= Lt /\
        forall (k : Nat) (s t : Real), s ∈ Set.Icc β ψ -> t ∈ Set.Icc β ψ ->
          forall a : Nat, a <= p ->
            forall y : SourceDomain (I := I) Φ k, (y : P.M) ∈ bf.grow k ->
              letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
              letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
              letI : T2Space (SourceDomain (I := I) Φ k) := sourceDomT2 (I := I) Φ k
              letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
              letI : SigmaCompactSpace (SourceDomain (I := I) Φ k) :=
                sourceDomSigmaOf (I := I) Φ k (hsrc k)
              metricDerivNorm (I := I) a (srcMetric (I := I) Φ hsrc htgt k s)
                (srcMetric (I := I) Φ hsrc htgt k t)
                (refRes (I := I) Φ R hsrc k) y <= Lt * |s - t|)
    (g0 : letI : TopologicalSpace P.M := P.topology;
      letI : ChartedSpace H P.M := P.charted; letI : IsManifold I ∞ P.M := P.smooth;
      SmoothRiemannianMetric I P.M)
    (h0 : (0 : Real) ∈ Set.Icc β ψ)
    (hcp : letI : TopologicalSpace P.M := P.topology;
        letI : ChartedSpace H P.M := P.charted; letI : T2Space P.M := P.t2;
        letI : IsManifold I ∞ P.M := P.smooth; letI : SigmaCompactSpace P.M := P.sigmaCompact;
      forall K : Set P.M, IsCompact K -> forall ε : Real, 0 < ε ->
        exists k0 : Nat, forall k : Nat, k0 <= k -> K ⊆ Φ.source k ∧
          (letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
           letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
           letI : T2Space (SourceDomain (I := I) Φ k) := sourceDomT2 (I := I) Φ k
           letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
           letI : SigmaCompactSpace (SourceDomain (I := I) Φ k) :=
             sourceDomSigmaOf (I := I) Φ k (hsrc k)
           metricDerivNormSupOn (I := I) (sourceCompactSet (I := I) Φ k K) 0
             (srcMetric (I := I) Φ hsrc htgt k 0)
             (resSrc (I := I) Φ hsrc k g0)
             (refRes (I := I) Φ R hsrc k) < ε)) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : IsManifold I ∞ P.M := P.smooth
    (endgameCo Φ R bf hsrc htgt β ψ hβψ hwin gRefT B Crel Bmax hBmax hCrel1 hBmax1 hequivT hrel hShiT hcovSrc hchi hlipG).gInf 0 = g0 :=
  gInf_zero_eq (I := I) Φ R bf hsrc htgt β ψ
    (endgameCo Φ R bf hsrc htgt β ψ hβψ hwin gRefT B Crel Bmax hBmax hCrel1 hBmax1 hequivT hrel hShiT hcovSrc hchi hlipG) h0 g0
    (conv0_of_cp (I := I) Φ R hsrc htgt g0 hcp)








omit [NeZero (Module.finrank ℝ E)] in
theorem flowLimit_endgame
    (mc : MetricCompactnessConclusion (I := I) (X.atZero (I := I)))
    (Φ₀ : PointedCGHMaps (I := I) X mc.limit mc.subseq)
    (R : letI : TopologicalSpace mc.limit.M := mc.limit.topology;
      letI : ChartedSpace H mc.limit.M := mc.limit.charted; letI : IsManifold I ∞ mc.limit.M := mc.limit.smooth;
      SmoothRiemannianMetric I mc.limit.M)
    (bf : BumpFamily (I := I) Φ₀) (hsrc : SrcSigma Φ₀) (htgt : TgtSigma Φ₀)
    (β ψ : Real) (hβψ : β <= ψ) (hwin : Set.Icc β ψ ⊆ X.D.regular)
    (gRefT : forall k : Nat,
      letI : TopologicalSpace (X.term (mc.subseq k)).M := (X.term (mc.subseq k)).topology
      letI : ChartedSpace H (X.term (mc.subseq k)).M := (X.term (mc.subseq k)).charted
      letI : IsManifold I ∞ (X.term (mc.subseq k)).M := (X.term (mc.subseq k)).smooth
      SmoothRiemannianMetric I ((X.term (mc.subseq k)).M))
    (B : Real -> Real) (Crel Bmax : Real)
    (hBmax : forall t : Real, t ∈ Set.Icc β ψ -> B t <= Bmax)
    (hCrel1 : 1 <= Crel) (hBmax1 : 1 <= Bmax)
    (hequivT : forall k : Nat,
      letI : TopologicalSpace (X.term (mc.subseq k)).M := (X.term (mc.subseq k)).topology
      letI : ChartedSpace H (X.term (mc.subseq k)).M := (X.term (mc.subseq k)).charted
      letI : T2Space (X.term (mc.subseq k)).M := (X.term (mc.subseq k)).t2
      letI : IsManifold I ∞ (X.term (mc.subseq k)).M := (X.term (mc.subseq k)).smooth
      letI : SigmaCompactSpace (X.term (mc.subseq k)).M := (X.term (mc.subseq k)).sigmaCompact
      MetricUniformEquivalentOnWindow (I := I) (Φ₀.target k) β ψ (gRefT k)
        (fun _ t => (X.term (mc.subseq k)).S.family.metric t) B)
    (hrel : forall k : Nat,
      letI : TopologicalSpace (SourceDomain (I := I) Φ₀ k) := sourceDomTop (I := I) Φ₀ k
      letI : ChartedSpace H (SourceDomain (I := I) Φ₀ k) := sourceDomCharted (I := I) Φ₀ k
      letI : T2Space (SourceDomain (I := I) Φ₀ k) := sourceDomT2 (I := I) Φ₀ k
      letI : IsManifold I ∞ (SourceDomain (I := I) Φ₀ k) := sourceDomSmooth (I := I) Φ₀ k
      MetricUniformEquivalentOn (I := I)
        (Set.univ : Set (SourceDomain (I := I) Φ₀ k))
        (refRes (I := I) Φ₀ R hsrc k)
        (tgtRefSrc (I := I) Φ₀ gRefT hsrc htgt k) Crel)
    (hShiT : forall N : Nat, exists KShi : Real, 0 <= KShi /\
      forall k : Nat,
        letI : TopologicalSpace (X.term (mc.subseq k)).M := (X.term (mc.subseq k)).topology
        letI : ChartedSpace H (X.term (mc.subseq k)).M := (X.term (mc.subseq k)).charted
        letI : T2Space (X.term (mc.subseq k)).M := (X.term (mc.subseq k)).t2
        letI : IsManifold I ∞ (X.term (mc.subseq k)).M := (X.term (mc.subseq k)).smooth
        letI : SigmaCompactSpace (X.term (mc.subseq k)).M := (X.term (mc.subseq k)).sigmaCompact
        MovingShiBoundOn (I := I) (Φ₀.target k) β ψ
          (fun _ t => (X.term (mc.subseq k)).S.family.metric t) N KShi)
    (hcovSrc : letI : TopologicalSpace mc.limit.M := mc.limit.topology;
        letI : ChartedSpace H mc.limit.M := mc.limit.charted; letI : T2Space mc.limit.M := mc.limit.t2;
        letI : IsManifold I ∞ mc.limit.M := mc.limit.smooth; letI : SigmaCompactSpace mc.limit.M := mc.limit.sigmaCompact;
      forall j : Nat, exists Cs : Real, 0 <= Cs /\
        forall (k : Nat) (t : Real), t ∈ Set.Icc β ψ ->
          forall y : SourceDomain (I := I) Φ₀ k, (y : mc.limit.M) ∈ tsupport (bf.chi k) ->
            letI : TopologicalSpace (SourceDomain (I := I) Φ₀ k) := sourceDomTop (I := I) Φ₀ k
            letI : ChartedSpace H (SourceDomain (I := I) Φ₀ k) := sourceDomCharted (I := I) Φ₀ k
            letI : T2Space (SourceDomain (I := I) Φ₀ k) := sourceDomT2 (I := I) Φ₀ k
            letI : IsManifold I ∞ (SourceDomain (I := I) Φ₀ k) := sourceDomSmooth (I := I) Φ₀ k
            letI : SigmaCompactSpace (SourceDomain (I := I) Φ₀ k) :=
              sourceDomSigmaOf (I := I) Φ₀ k (hsrc k)
            metricCovDerivNorm (I := I) j (srcMetric (I := I) Φ₀ hsrc htgt k t)
              (refRes (I := I) Φ₀ R hsrc k) y <= Cs)
    (hchi : letI : TopologicalSpace mc.limit.M := mc.limit.topology;
        letI : ChartedSpace H mc.limit.M := mc.limit.charted; letI : T2Space mc.limit.M := mc.limit.t2;
        letI : IsManifold I ∞ mc.limit.M := mc.limit.smooth; letI : SigmaCompactSpace mc.limit.M := mc.limit.sigmaCompact;
      forall c : Nat, exists Cc : Real, 0 <= Cc /\
        forall (k : Nat) (y : SourceDomain (I := I) Φ₀ k),
          letI : TopologicalSpace (SourceDomain (I := I) Φ₀ k) := sourceDomTop (I := I) Φ₀ k
          letI : ChartedSpace H (SourceDomain (I := I) Φ₀ k) := sourceDomCharted (I := I) Φ₀ k
          letI : T2Space (SourceDomain (I := I) Φ₀ k) := sourceDomT2 (I := I) Φ₀ k
          letI : IsManifold I ∞ (SourceDomain (I := I) Φ₀ k) := sourceDomSmooth (I := I) Φ₀ k
          letI : SigmaCompactSpace (SourceDomain (I := I) Φ₀ k) :=
            sourceDomSigmaOf (I := I) Φ₀ k (hsrc k)
          Real.sqrt (Tensor0SBundle.normSq0S (I := I)
            (refRes (I := I) Φ₀ R hsrc k) y (0 + c)
            (iterCov (I := I) (refRes (I := I) Φ₀ R hsrc k) 0
              (Tensor0SField.fromScalarField (𝕜 := Real) (E := E) (H := H) (I := I)
                (M := SourceDomain (I := I) Φ₀ k) (∞ : WithTop ℕ∞)
                (chiRes (I := I) Φ₀ bf k) (chiRes_smooth (I := I) Φ₀ bf k)) c y)) <= Cc)
    (hlipG : letI : TopologicalSpace mc.limit.M := mc.limit.topology;
        letI : ChartedSpace H mc.limit.M := mc.limit.charted; letI : T2Space mc.limit.M := mc.limit.t2;
        letI : IsManifold I ∞ mc.limit.M := mc.limit.smooth; letI : SigmaCompactSpace mc.limit.M := mc.limit.sigmaCompact;
      forall p : Nat, exists Lt : Real, 0 <= Lt /\
        forall (k : Nat) (s t : Real), s ∈ Set.Icc β ψ -> t ∈ Set.Icc β ψ ->
          forall a : Nat, a <= p ->
            forall y : SourceDomain (I := I) Φ₀ k, (y : mc.limit.M) ∈ bf.grow k ->
              letI : TopologicalSpace (SourceDomain (I := I) Φ₀ k) := sourceDomTop (I := I) Φ₀ k
              letI : ChartedSpace H (SourceDomain (I := I) Φ₀ k) := sourceDomCharted (I := I) Φ₀ k
              letI : T2Space (SourceDomain (I := I) Φ₀ k) := sourceDomT2 (I := I) Φ₀ k
              letI : IsManifold I ∞ (SourceDomain (I := I) Φ₀ k) := sourceDomSmooth (I := I) Φ₀ k
              letI : SigmaCompactSpace (SourceDomain (I := I) Φ₀ k) :=
                sourceDomSigmaOf (I := I) Φ₀ k (hsrc k)
              metricDerivNorm (I := I) a (srcMetric (I := I) Φ₀ hsrc htgt k s)
                (srcMetric (I := I) Φ₀ hsrc htgt k t)
                (refRes (I := I) Φ₀ R hsrc k) y <= Lt * |s - t|)
    (hcarrier : X.D.carrier ⊆ Set.Icc β ψ)
    (h0 : (0 : Real) ∈ Set.Icc β ψ)
    (hcp : letI : TopologicalSpace mc.limit.M := mc.limit.topology;
        letI : ChartedSpace H mc.limit.M := mc.limit.charted; letI : T2Space mc.limit.M := mc.limit.t2;
        letI : IsManifold I ∞ mc.limit.M := mc.limit.smooth;
        letI : SigmaCompactSpace mc.limit.M := mc.limit.sigmaCompact;
      forall K : Set mc.limit.M, IsCompact K -> forall ε : Real, 0 < ε ->
        exists k0 : Nat, forall k : Nat, k0 <= k -> K ⊆ Φ₀.source k ∧
          (letI : TopologicalSpace (SourceDomain (I := I) Φ₀ k) := sourceDomTop (I := I) Φ₀ k
           letI : ChartedSpace H (SourceDomain (I := I) Φ₀ k) := sourceDomCharted (I := I) Φ₀ k
           letI : T2Space (SourceDomain (I := I) Φ₀ k) := sourceDomT2 (I := I) Φ₀ k
           letI : IsManifold I ∞ (SourceDomain (I := I) Φ₀ k) := sourceDomSmooth (I := I) Φ₀ k
           letI : SigmaCompactSpace (SourceDomain (I := I) Φ₀ k) :=
             sourceDomSigmaOf (I := I) Φ₀ k (hsrc k)
           metricDerivNormSupOn (I := I) (sourceCompactSet (I := I) Φ₀ k K) 0
             (srcMetric (I := I) Φ₀ hsrc htgt k 0)
             (resSrc (I := I) Φ₀ hsrc k mc.limit.metric)
             (refRes (I := I) Φ₀ R hsrc k) < ε))
    (hsol :
      letI : TopologicalSpace mc.limit.M := mc.limit.topology
      letI : ChartedSpace H mc.limit.M := mc.limit.charted
      letI : IsManifold I ∞ mc.limit.M := mc.limit.smooth
      letI : SigmaCompactSpace mc.limit.M := mc.limit.sigmaCompact
      letI : T2Space mc.limit.M := mc.limit.t2
      letI : IsManifold I 1 mc.limit.M :=
        IsManifold.of_le (I := I) (M := mc.limit.M) (n := ∞)
          (by decide : (1 : WithTop ℕ∞) ≤ ∞)
      letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) mc.limit.M := by
        change IsManifold I ∞ mc.limit.M
        infer_instance
      DifferentialGeometry.PDE.RicciFlow.IsSolutionOn (I := I)
        ({ base := { metric := (endgameCo Φ₀ R bf hsrc htgt β ψ hβψ hwin gRefT B Crel Bmax hBmax hCrel1 hBmax1 hequivT hrel hShiT hcovSrc hchi hlipG).gInf } } :
          DifferentialGeometry.PDE.RicciFlow.SolutionOn (I := I) (M := mc.limit.M) X.D))
    (scalar : ScalarPullbackTendsto (I := I)
      ((flowOfMetric_atTime (I := I) X.D mc.limit (endgameCo Φ₀ R bf hsrc htgt β ψ hβψ hwin gRefT B Crel Bmax hBmax hCrel1 hBmax1 hequivT hrel hShiT hcovSrc hchi hlipG).gInf hsol 0
          (endgameCo_zero Φ₀ R bf hsrc htgt β ψ hβψ hwin gRefT B Crel Bmax hBmax hCrel1 hBmax1
            hequivT hrel hShiT hcovSrc hchi hlipG mc.limit.metric h0 hcp)).symm ▸
        (Φ₀.compSubseq (endgameCo Φ₀ R bf hsrc htgt β ψ hβψ hwin gRefT B Crel Bmax hBmax hCrel1 hBmax1 hequivT hrel hShiT hcovSrc hchi hlipG).φ (endgameCo Φ₀ R bf hsrc htgt β ψ hβψ hwin gRefT B Crel Bmax hBmax hCrel1 hBmax1 hequivT hrel hShiT hcovSrc hchi hlipG).hφ) :
        PointedCGHMaps (I := I) X
          ((flowOfMetric (I := I) X.D mc.limit (endgameCo Φ₀ R bf hsrc htgt β ψ hβψ hwin gRefT B Crel Bmax hBmax hCrel1 hBmax1 hequivT hrel hShiT hcovSrc hchi hlipG).gInf hsol).atTime 0)
          (mc.subseq ∘ (endgameCo Φ₀ R bf hsrc htgt β ψ hβψ hwin gRefT B Crel Bmax hBmax hCrel1 hBmax1 hequivT hrel hShiT hcovSrc hchi hlipG).φ))) :
    CompactnessConclusion (I := I) X :=
  flowLimit_of_mc (I := I) mc Φ₀ R bf hsrc htgt β ψ hcarrier (endgameCo Φ₀ R bf hsrc htgt β ψ hβψ hwin gRefT B Crel Bmax hBmax hCrel1 hBmax1 hequivT hrel hShiT hcovSrc hchi hlipG)
    (endgameCo_zero Φ₀ R bf hsrc htgt β ψ hβψ hwin gRefT B Crel Bmax hBmax hCrel1 hBmax1
      hequivT hrel hShiT hcovSrc hchi hlipG mc.limit.metric h0 hcp)
    hsol scalar

end Endgame

end HCGCompactness
end DifferentialGeometry
