import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepCProducers
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.NormalPhaseEndpoint

set_option autoImplicit false










noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Set Bundle Manifold
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}



private theorem exists_exit_time
    {Z : Type*} [TopologicalSpace Z] {K : Set Z} (hK : IsClosed K)
    {gamma : Real → Z} {b : Real} (hb : 0 < b)
    (hgamma : ContinuousOn gamma (Set.Icc 0 b))
    (hzero : gamma 0 ∈ interior K) (hone : gamma b ∉ K) :
    ∃ t : Real, t ∈ Set.Ioc 0 b ∧
      (∀ s ∈ Set.Icc 0 t, gamma s ∈ K) ∧ gamma t ∈ frontier K := by
  let T := Set.Icc (0 : Real) b
  letI : CompactSpace T := isCompact_iff_compactSpace.mp isCompact_Icc
  let gammaT : T → Z := fun t ↦ gamma t
  let B : Set T := gammaT ⁻¹' (interior K)ᶜ
  have hgammaT : Continuous gammaT := hgamma.restrict
  have hBclosed : IsClosed B := by
    exact isOpen_interior.isClosed_compl.preimage hgammaT
  have honeB : (⟨b, by simp [T, hb.le]⟩ : T) ∈ B := by
    change gamma b ∉ interior K
    exact fun h ↦ hone (interior_subset h)
  have hBne : B.Nonempty := ⟨⟨b, by simp [T, hb.le]⟩, honeB⟩
  obtain ⟨t, htB, htmin⟩ :=
    hBclosed.isCompact.exists_isMinOn hBne continuous_subtype_val.continuousOn
  have htNot : gamma (t : Real) ∉ interior K := by
    simpa only [B, gammaT, Set.mem_preimage, Set.mem_compl_iff] using htB
  have htne : (t : Real) ≠ 0 := by
    intro ht
    apply htNot
    simpa only [ht] using hzero
  have htpos : (0 : Real) < t := lt_of_le_of_ne t.property.1 (Ne.symm htne)
  have hbefore : ∀ s ∈ Set.Ico (0 : Real) t, gamma s ∈ interior K := by
    intro s hs
    by_contra hsNot
    let sT : T := ⟨s, hs.1, (le_of_lt hs.2).trans t.property.2⟩
    have hsB : sT ∈ B := by
      change gamma s ∉ interior K
      exact hsNot
    exact (not_le_of_gt hs.2) (htmin hsB)
  have htClosure : (t : Real) ∈ closure (Set.Ico (0 : Real) t) := by
    rw [closure_Ico (Ne.symm htne)]
    exact ⟨htpos.le, le_rfl⟩
  have hcont : ContinuousWithinAt gamma (Set.Ico (0 : Real) t) t :=
    (hgamma t t.property).mono fun s hs ↦
      ⟨hs.1, (le_of_lt hs.2).trans t.property.2⟩
  have htKclosure : gamma t ∈ closure K :=
    hcont.mem_closure htClosure fun s hs ↦ interior_subset (hbefore s hs)
  have htK : gamma t ∈ K := by
    simpa only [hK.closure_eq] using htKclosure
  refine ⟨t, ⟨htpos, t.property.2⟩, ?_, ?_⟩
  · intro s hs
    by_cases hst : s = t
    · simpa only [hst] using htK
    · exact interior_subset (hbefore s ⟨hs.1, lt_of_le_of_ne hs.2 hst⟩)
  · rw [frontier, hK.closure_eq]
    exact ⟨htK, htNot⟩




private theorem NormalCoordMetricEquivOn.chart_join_le
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (hcomplete : MetricComplete (I := I) Y)
    (hconn :
      letI : TopologicalSpace Y.M := Y.topology
      ConnectedSpace Y.M)
    (hEnorm :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : RiemannianBundle (fun x : Y.M ↦ TangentSpace I x) :=
        Y.riemBundle (I := I)
      ∀ (x : Y.M) (v : TangentSpace I x),
        ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (Y.metric.inner x v v)))
    {c : Y.M} {U : Set E}
    (h : NormalCoordMetricEquivOn (I := I) Y c U)
    {x y : Y.M} {t : Real} (ht : t ∈ Set.Icc (0 : Real) 1)
    (hjoin :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : IsManifold I 1 Y.M := IsManifold.of_le
        (I := I) (M := Y.M) (n := ∞) (by decide)
      letI : SigmaCompactSpace Y.M := Y.sigmaCompact
      letI : T2Space Y.M := Y.t2
      letI : ConnectedSpace Y.M := hconn
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      letI : TopologicalSpace.MetrizableSpace Y.M :=
        Manifold.metrizableSpace I Y.M
      letI : T3Space Y.M := inferInstance
      letI : RiemannianBundle (fun z : Y.M ↦ TangentSpace I z) :=
        Y.riemBundle (I := I)
      letI : (z : Y.M) → InnerProductSpace Real (TangentSpace I z) :=
        Y.riemInner (I := I)
      letI : IsContinuousRiemannianBundle E
          (fun z : Y.M ↦ TangentSpace I z) := Y.riemBundle_cont (I := I)
      letI : EMetricSpace Y.M := Y.emetricSpace (I := I)
      letI : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
      Set.MapsTo (minJoin (I := I) Y.metric hEnorm x y)
        (Set.Icc (0 : Real) t)
        ((normalChartAt (I := I) Y.metric c).source ∩
          (normalChartAt (I := I) Y.metric c) ⁻¹' U)) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : IsManifold I 1 Y.M := IsManifold.of_le
      (I := I) (M := Y.M) (n := ∞) (by decide)
    letI : SigmaCompactSpace Y.M := Y.sigmaCompact
    letI : T2Space Y.M := Y.t2
    letI : ConnectedSpace Y.M := hconn
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    letI : TopologicalSpace.MetrizableSpace Y.M :=
      Manifold.metrizableSpace I Y.M
    letI : T3Space Y.M := inferInstance
    letI : RiemannianBundle (fun z : Y.M ↦ TangentSpace I z) :=
      Y.riemBundle (I := I)
    letI : (z : Y.M) → InnerProductSpace Real (TangentSpace I z) :=
      Y.riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
        (fun z : Y.M ↦ TangentSpace I z) := Y.riemBundle_cont (I := I)
    letI : EMetricSpace Y.M := Y.emetricSpace (I := I)
    letI : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
    dist (normalChartAt (I := I) Y.metric c x)
        (normalChartAt (I := I) Y.metric c
          (minJoin (I := I) Y.metric hEnorm x y t)) ≤
      Real.sqrt 2 * (riemannianEDist I x y).toReal * t := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : IsManifold I 1 Y.M := IsManifold.of_le
    (I := I) (M := Y.M) (n := ∞) (by decide)
  letI : SigmaCompactSpace Y.M := Y.sigmaCompact
  letI : T2Space Y.M := Y.t2
  letI : ConnectedSpace Y.M := hconn
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  letI : TopologicalSpace.MetrizableSpace Y.M :=
    Manifold.metrizableSpace I Y.M
  letI : T3Space Y.M := inferInstance
  letI : RiemannianBundle (fun z : Y.M ↦ TangentSpace I z) :=
    Y.riemBundle (I := I)
  letI : (z : Y.M) → InnerProductSpace Real (TangentSpace I z) :=
    Y.riemInner (I := I)
  letI : IsContinuousRiemannianBundle E
      (fun z : Y.M ↦ TangentSpace I z) := Y.riemBundle_cont (I := I)
  letI : EMetricSpace Y.M := Y.emetricSpace (I := I)
  letI : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
  let w : TangentSpace I x := minimizingVec (I := I) Y.metric hEnorm x y
  let gamma : Real → Y.M := minJoin (I := I) Y.metric hEnorm x y
  let chi := normalChartAt (I := I) Y.metric c
  let e := expMapDiffeo (I := I) Y.metric c
  let eta : Real → E := chi ∘ gamma
  let d : Real := (riemannianEDist I x y).toReal
  have hd : 0 ≤ d := ENNReal.toReal_nonneg
  have hgammaCont : Continuous gamma := by
    simpa only [gamma] using minJoin_cont (I := I) Y.metric hEnorm x y
  have hdiff : ∀ s ∈ Set.Icc (0 : Real) t,
      DifferentiableAt Real eta s := by
    intro s hs
    have hgammaDiff : MDifferentiableAt 𝓘(Real, Real) I gamma s := by
      have hsmooth := intrinsicGeodesic_contMDiffOn
        (I := I) Y.metric hEnorm x w
      have hm := hsmooth.mdifferentiableOn one_ne_zero s (Set.mem_univ s)
      simpa only [gamma, minJoin, w] using
        hm.mdifferentiableAt (isOpen_univ.mem_nhds (Set.mem_univ s))
    have hchiDiff : MDifferentiableAt I 𝓘(Real, E) chi (gamma s) :=
      (chi.contMDiffOn_toFun.mdifferentiableOn one_ne_zero _
        (hjoin hs).1).mdifferentiableAt
          (chi.open_source.mem_nhds (hjoin hs).1)
    exact mdifferentiableAt_iff_differentiableAt.mp
      (by simpa only [eta] using hchiDiff.comp s hgammaDiff)
  have hbound : ∀ s ∈ Set.Icc (0 : Real) t,
      ‖deriv eta s‖ ≤ Real.sqrt 2 * d := by
    intro s hs
    have hgammaDiff : MDifferentiableAt 𝓘(Real, Real) I gamma s := by
      have hsmooth := intrinsicGeodesic_contMDiffOn
        (I := I) Y.metric hEnorm x w
      have hm := hsmooth.mdifferentiableOn one_ne_zero s (Set.mem_univ s)
      simpa only [gamma, minJoin, w] using
        hm.mdifferentiableAt (isOpen_univ.mem_nhds (Set.mem_univ s))
    have hchiDiff : MDifferentiableAt I 𝓘(Real, E) chi (gamma s) :=
      (chi.contMDiffOn_toFun.mdifferentiableOn one_ne_zero _
        (hjoin hs).1).mdifferentiableAt
          (chi.open_source.mem_nhds (hjoin hs).1)
    have hetaDiff : MDifferentiableAt 𝓘(Real, Real) 𝓘(Real, E) eta s := by
      simpa only [eta] using hchiDiff.comp s hgammaDiff
    have hetaSrc : eta s ∈ e.source := by
      rw [← normalChartAt_target_eq (I := I)]
      exact chi.map_source (hjoin hs).1
    have heDiff : MDifferentiableAt 𝓘(Real, E) I e (eta s) :=
      (e.contMDiffOn_toFun.mdifferentiableOn one_ne_zero _ hetaSrc).mdifferentiableAt
        (e.open_source.mem_nhds hetaSrc)
    have hnear : ∀ᶠ q in nhds s, gamma q ∈ chi.source :=
      hgammaCont.continuousAt.eventually (chi.open_source.mem_nhds (hjoin hs).1)
    have heq : e ∘ eta =ᶠ[nhds s] gamma := by
      filter_upwards [hnear] with q hq
      change chi.symm (chi (gamma q)) = gamma q
      exact chi.left_inv hq
    have hcomp :
        (mfderiv 𝓘(Real, E) I e (eta s)).comp
            (mfderiv 𝓘(Real, Real) 𝓘(Real, E) eta s) =
          mfderiv 𝓘(Real, Real) I gamma s := by
      have hderiv := Filter.EventuallyEq.mfderiv_eq
        (I := 𝓘(Real, Real)) (I' := I) heq
      rw [mfderiv_comp s heDiff hetaDiff] at hderiv
      simpa only using hderiv
    have hetaVel : mfderiv 𝓘(Real, Real) 𝓘(Real, E) eta s 1 =
        deriv eta s := by
      rw [mfderiv_eq_fderiv]
      exact fderiv_apply_one_eq_deriv
    have hvel : mfderiv 𝓘(Real, E) I e (eta s) (deriv eta s) =
        mfderiv 𝓘(Real, Real) I gamma s 1 := by
      have hv := DFunLike.congr_fun hcomp (1 : Real)
      change (mfderiv 𝓘(Real, E) I e (eta s))
          (mfderiv 𝓘(Real, Real) 𝓘(Real, E) eta s 1) =
        mfderiv 𝓘(Real, Real) I gamma s 1 at hv
      rw [hetaVel] at hv
      exact hv
    have hlaunch : Y.metric.inner x w w = d ^ 2 := by
      have hnonneg : 0 ≤ Y.metric.inner x w w :=
        gInner_self_nonneg (I := I) Y.metric x w
      calc
        Y.metric.inner x w w = (Real.sqrt (Y.metric.inner x w w)) ^ 2 :=
          (Real.sq_sqrt hnonneg).symm
        _ = d ^ 2 := by
          rw [minimizingVec_len (I := I) Y.metric hEnorm x y]
    have hspeed : Y.metric.inner (gamma s)
          (mfderiv 𝓘(Real, Real) I gamma s 1)
          (mfderiv 𝓘(Real, Real) I gamma s 1) = d ^ 2 := by
      calc
        _ = Y.metric.inner x w w := by
          simpa only [gamma, minJoin, w] using
            intrinsicGeodesic_speedSq_eq (I := I) Y.metric hEnorm x w s
        _ = d ^ 2 := hlaunch
    have hbase : e (eta s) = gamma s := heq.self_of_nhds
    have hmetric : normalCoordMetric (I := I) Y c (eta s)
          (deriv eta s) (deriv eta s) = d ^ 2 := by
      rw [normalCoordMetric_apply (I := I), hbase]
      change Y.metric.inner (gamma s)
          (mfderiv 𝓘(Real, E) I e (eta s) (deriv eta s))
          (mfderiv 𝓘(Real, E) I e (eta s) (deriv eta s)) = d ^ 2
      rw [hvel]
      exact hspeed
    have hlower := (h (eta s) (hjoin hs).2 (deriv eta s)).1
    rw [hmetric] at hlower
    have hsq : ‖deriv eta s‖ ^ 2 ≤ (Real.sqrt 2 * d) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : Real) ≤ 2)]
      nlinarith
    exact le_of_sq_le_sq hsq (mul_nonneg (Real.sqrt_nonneg 2) hd)
  have hmean := Convex.norm_image_sub_le_of_norm_deriv_le
    (f := eta) hdiff hbound (convex_Icc (0 : Real) t)
    (left_mem_Icc.mpr ht.1) (right_mem_Icc.mpr ht.1)
  have hend : dist (chi x) (chi (gamma t)) = ‖eta t - eta 0‖ := by
    simp only [eta, gamma, Function.comp_apply, minJoin_zero,
      dist_eq_norm, norm_sub_rev]
  rw [hend]
  have ht_abs : |t| = t := abs_of_nonneg ht.1
  simpa only [Real.norm_eq_abs, sub_zero, ht_abs, d, mul_assoc] using hmean





theorem NormalCoordMetricEquivOn.ball_core_dist
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (hcomplete : MetricComplete (I := I) Y)
    (hconn :
      letI : TopologicalSpace Y.M := Y.topology
      ConnectedSpace Y.M)
    (hEnorm :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : RiemannianBundle (fun x : Y.M ↦ TangentSpace I x) :=
        Y.riemBundle (I := I)
      ∀ (x : Y.M) (v : TangentSpace I x),
        ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (Y.metric.inner x v v)))
    {c : Y.M} {U C : Set E}
    (h : NormalCoordMetricEquivOn (I := I) Y c U)
    (hCU : C ⊆ U)
    (hUtgt :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      U ⊆ (normalChartAt (I := I) Y.metric c).target)
    {z : E} {eta rho : Real} (heta : 0 < eta)
    (hclosed : Metric.closedBall z eta ⊆ interior C)
    (hrhoeta : Real.sqrt 2 * rho < eta) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : IsManifold I 1 Y.M := IsManifold.of_le
      (I := I) (M := Y.M) (n := ∞) (by decide)
    letI : SigmaCompactSpace Y.M := Y.sigmaCompact
    letI : T2Space Y.M := Y.t2
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    letI : RiemannianBundle (fun x : Y.M ↦ TangentSpace I x) :=
      Y.riemBundle (I := I)
    {x | (riemannianEDist I
      ((normalChartAt (I := I) Y.metric c).symm z) x).toReal < rho} ⊆
      {x | x ∈ (normalChartAt (I := I) Y.metric c).symm '' interior C ∧
        dist ((normalChartAt (I := I) Y.metric c) x) z ≤
          Real.sqrt 2 * (riemannianEDist I
            ((normalChartAt (I := I) Y.metric c).symm z) x).toReal} := by
  classical
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : IsManifold I 1 Y.M := IsManifold.of_le
    (I := I) (M := Y.M) (n := ∞) (by decide)
  letI : SigmaCompactSpace Y.M := Y.sigmaCompact
  letI : T2Space Y.M := Y.t2
  letI : ConnectedSpace Y.M := hconn
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  letI : TopologicalSpace.MetrizableSpace Y.M :=
    Manifold.metrizableSpace I Y.M
  letI : T3Space Y.M := inferInstance
  letI : RiemannianBundle (fun x : Y.M ↦ TangentSpace I x) :=
    Y.riemBundle (I := I)
  letI : (x : Y.M) → InnerProductSpace Real (TangentSpace I x) :=
    Y.riemInner (I := I)
  letI : IsContinuousRiemannianBundle E
      (fun x : Y.M ↦ TangentSpace I x) := Y.riemBundle_cont (I := I)
  letI : EMetricSpace Y.M := Y.emetricSpace (I := I)
  letI : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
  letI : MetricSpace Y.M := HopfRinow.riemMetricSpace (I := I) (M := Y.M)
  let chi := normalChartAt (I := I) Y.metric c
  let B := Metric.closedBall z eta
  let K : Set Y.M := chi.symm '' B
  have hBC : B ⊆ interior C := hclosed
  have hBU : B ⊆ U := hBC.trans (interior_subset.trans hCU)
  have hBtgt : B ⊆ chi.target := hBU.trans hUtgt
  have hBcompact : IsCompact B := isCompact_closedBall z eta
  have hsymmCont : ContinuousOn chi.symm chi.target :=
    chi.symm.contMDiffOn_toFun.continuousOn
  have hKcompact : IsCompact K :=
    hBcompact.image_of_continuousOn (hsymmCont.mono hBtgt)
  have hKclosed : IsClosed K := hKcompact.isClosed
  have hballB : Metric.ball z eta ⊆ B := Metric.ball_subset_closedBall
  have hballtgt : Metric.ball z eta ⊆ chi.target := hballB.trans hBtgt
  let O : Set Y.M := chi.symm '' Metric.ball z eta
  have hOopen : IsOpen O :=
    chi.symm.toOpenPartialHomeomorph.isOpen_image_of_subset_source
      Metric.isOpen_ball hballtgt
  have hzball : z ∈ Metric.ball z eta := Metric.mem_ball_self heta
  have hyO : chi.symm z ∈ O := ⟨z, hzball, rfl⟩
  have hOK : O ⊆ K := Set.image_mono hballB
  have hyInt : chi.symm z ∈ interior K :=
    (interior_maximal hOK hOopen) hyO
  intro x hx
  let gamma : Real → Y.M :=
    minJoin (I := I) Y.metric hEnorm (chi.symm z) x
  have hgammaCont : Continuous gamma := by
    simpa only [gamma] using
      minJoin_cont (I := I) Y.metric hEnorm (chi.symm z) x
  have hgammaZero : gamma 0 = chi.symm z := by
    simp only [gamma, minJoin_zero]
  have hgammaOne : gamma 1 = x := by
    simp only [gamma, minJoin_one]
  have hzTgt : z ∈ chi.target := hBtgt (Metric.mem_closedBall_self heta.le)
  have hchiZ : chi (chi.symm z) = z := chi.right_inv hzTgt
  have hgammaK : Set.MapsTo gamma (Set.Icc (0 : Real) 1) K := by
    intro q hq
    by_contra hqK
    have hqne : q ≠ 0 := by
      intro hqzero
      apply hqK
      simpa only [hqzero, hgammaZero] using interior_subset hyInt
    have hqpos : 0 < q := lt_of_le_of_ne hq.1 (Ne.symm hqne)
    obtain ⟨t, ht, hstay, hfront⟩ := exists_exit_time hKclosed hqpos
      (hgammaCont.continuousOn.mono (show
        Set.Icc (0 : Real) q ⊆ Set.Icc 0 1 from by
          intro s hs
          exact ⟨hs.1, hs.2.trans hq.2⟩))
      (by simpa only [hgammaZero] using hyInt) hqK
    have hfront' : gamma t ∈ K ∧ gamma t ∉ interior K := by
      rw [frontier, hKclosed.closure_eq] at hfront
      exact hfront
    obtain ⟨w, hwB, hwgamma⟩ := hfront'.1
    have hwTgt : w ∈ chi.target := hBtgt hwB
    have hchiGamma : chi (gamma t) = w := by
      rw [← hwgamma]
      exact chi.right_inv hwTgt
    have hwNotBall : w ∉ Metric.ball z eta := by
      intro hwball
      apply hfront'.2
      exact (interior_maximal hOK hOopen) ⟨w, hwball, hwgamma⟩
    have hwDist : dist z w = eta := by
      have hwle : dist w z ≤ eta := Metric.mem_closedBall.mp hwB
      have hwnlt : ¬ dist w z < eta := by
        simpa only [Metric.mem_ball, dist_comm] using hwNotBall
      rw [dist_comm]
      exact le_antisymm hwle (not_lt.mp hwnlt)
    have hjoin : Set.MapsTo gamma (Set.Icc (0 : Real) t)
        (chi.source ∩ chi ⁻¹' U) := by
      intro s hs
      obtain ⟨v, hvB, hvgamma⟩ := hstay s hs
      have hvTgt : v ∈ chi.target := hBtgt hvB
      have hsrc : gamma s ∈ chi.source := by
        rw [← hvgamma]
        exact chi.symm_mapsTo hvTgt
      have hchi : chi (gamma s) = v := by
        rw [← hvgamma]
        exact chi.right_inv hvTgt
      refine ⟨hsrc, ?_⟩
      change chi (gamma s) ∈ U
      rw [hchi]
      exact hBU hvB
    have htunit : t ∈ Set.Icc (0 : Real) 1 :=
      ⟨ht.1.le, ht.2.trans hq.2⟩
    have hprefix := NormalCoordMetricEquivOn.chart_join_le Y hcomplete hconn
      hEnorm h htunit hjoin
    have hcoord : eta ≤
        Real.sqrt 2 * (riemannianEDist I (chi.symm z) x).toReal * t := by
      have heq : dist (chi (chi.symm z)) (chi (gamma t)) = eta := by
        rw [hchiZ, hchiGamma, hwDist]
      calc
        eta = dist (chi (chi.symm z)) (chi (gamma t)) := heq.symm
        _ ≤ Real.sqrt 2 * (riemannianEDist I (chi.symm z) x).toReal * t := by
          simpa only [gamma] using hprefix
    have hsqrt : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    have hdnonneg : 0 ≤ (riemannianEDist I (chi.symm z) x).toReal :=
      ENNReal.toReal_nonneg
    have hsmall : Real.sqrt 2 *
        (riemannianEDist I (chi.symm z) x).toReal * t <
          Real.sqrt 2 * rho := by
      have hfirst : Real.sqrt 2 *
          (riemannianEDist I (chi.symm z) x).toReal < Real.sqrt 2 * rho :=
        mul_lt_mul_of_pos_left hx (Real.sqrt_pos.2 (by norm_num))
      calc
        Real.sqrt 2 * (riemannianEDist I (chi.symm z) x).toReal * t ≤
            Real.sqrt 2 * (riemannianEDist I (chi.symm z) x).toReal * 1 :=
          mul_le_mul_of_nonneg_left htunit.2 (mul_nonneg hsqrt hdnonneg)
        _ < Real.sqrt 2 * rho := by simpa only [mul_one] using hfirst
    linarith
  have hxK : x ∈ K := by
    have hxK' := hgammaK (by simp : (1 : Real) ∈ Set.Icc 0 1)
    simpa only [hgammaOne] using hxK'
  obtain ⟨w, hwB, hwx⟩ := hxK
  have hxcore : x ∈ chi.symm '' interior C := ⟨w, hBC hwB, hwx⟩
  have hjoin : Set.MapsTo gamma (Set.Icc (0 : Real) 1)
      (chi.source ∩ chi ⁻¹' U) := by
    intro q hq
    obtain ⟨v, hvB, hvgamma⟩ := hgammaK hq
    have hvTgt : v ∈ chi.target := hBtgt hvB
    have hsrc : gamma q ∈ chi.source := by
      rw [← hvgamma]
      exact chi.symm_mapsTo hvTgt
    have hchi : chi (gamma q) = v := by
      rw [← hvgamma]
      exact chi.right_inv hvTgt
    refine ⟨hsrc, ?_⟩
    change chi (gamma q) ∈ U
    rw [hchi]
    exact hBU hvB
  have hfull := NormalCoordMetricEquivOn.chart_join_le Y hcomplete hconn
    hEnorm h (by simp : (1 : Real) ∈ Set.Icc 0 1) hjoin
  have hcoord : dist (chi x) z ≤
      Real.sqrt 2 * (riemannianEDist I (chi.symm z) x).toReal := by
    have hfull' : dist (chi (chi.symm z)) (chi x) ≤
        Real.sqrt 2 * (riemannianEDist I (chi.symm z) x).toReal := by
      simpa only [gamma, minJoin_one, mul_one] using hfull
    calc
      dist (chi x) z = dist (chi (chi.symm z)) (chi x) := by
        rw [hchiZ, dist_comm]
      _ ≤ Real.sqrt 2 * (riemannianEDist I (chi.symm z) x).toReal := hfull'
  exact ⟨hxcore, hcoord⟩



theorem NormalCoordMetricEquivOn.ball_subset_core
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (hcomplete : MetricComplete (I := I) Y)
    (hconn :
      letI : TopologicalSpace Y.M := Y.topology
      ConnectedSpace Y.M)
    (hEnorm :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : RiemannianBundle (fun x : Y.M ↦ TangentSpace I x) :=
        Y.riemBundle (I := I)
      ∀ (x : Y.M) (v : TangentSpace I x),
        ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (Y.metric.inner x v v)))
    {c : Y.M} {U C : Set E}
    (h : NormalCoordMetricEquivOn (I := I) Y c U)
    (hCU : C ⊆ U)
    (hUtgt :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      U ⊆ (normalChartAt (I := I) Y.metric c).target)
    {z : E} {eta rho : Real} (heta : 0 < eta)
    (hclosed : Metric.closedBall z eta ⊆ interior C)
    (hrhoeta : Real.sqrt 2 * rho < eta) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : IsManifold I 1 Y.M := IsManifold.of_le
      (I := I) (M := Y.M) (n := ∞) (by decide)
    letI : SigmaCompactSpace Y.M := Y.sigmaCompact
    letI : T2Space Y.M := Y.t2
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    letI : RiemannianBundle (fun x : Y.M ↦ TangentSpace I x) :=
      Y.riemBundle (I := I)
    {x | (riemannianEDist I
      ((normalChartAt (I := I) Y.metric c).symm z) x).toReal < rho} ⊆
      (normalChartAt (I := I) Y.metric c).symm '' interior C := by
  intro x hx
  exact (NormalCoordMetricEquivOn.ball_core_dist Y hcomplete hconn hEnorm
    h hCU hUtgt heta hclosed hrhoeta hx).1





theorem HasSuppConvData.metric_buffer
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
    (hcomplete : ∀ j, MetricComplete (I := I) (X.obj j))
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M) :
    let Lphi := L.subseq hphi
    ∃ rho : Real, 0 < rho ∧ ∀ k,
      let Y := X.obj (Lphi.φ k)
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space Y.M := Y.t2
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      letI : MetricSpace Y.M := (P (Lphi.φ k)).ms
      ∀ y ∈ Lphi.hatSourceBall inp.decay P r k,
        ∃ (alpha : LiveSlot L inp.pack r) (z : E),
          (normalChartAt (I := I) Y.metric
            (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))).symm z = y ∧
          Metric.ball y rho ⊆
            (normalChartAt (I := I) Y.metric
              (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))).symm ''
                interior (C0 alpha) ∧
          ∀ x ∈ Metric.ball y rho,
            dist
                ((normalChartAt (I := I) Y.metric
                  (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))) x) z ≤
              Real.sqrt 2 * inp.decay.dist (Lphi.φ k) x y := by
  classical
  let Lphi := L.subseq hphi
  obtain ⟨eta, heta, hbuffer⟩ :=
    h.buffer_cover inp P L r hr U C0 C1 aInf Jinf Jbarinf
  let Yzero := X.obj (Lphi.φ 0)
  letI : TopologicalSpace Yzero.M := Yzero.topology
  letI : ChartedSpace H Yzero.M := Yzero.charted
  letI : IsManifold I ∞ Yzero.M := Yzero.smooth
  letI : T2Space Yzero.M := Yzero.t2
  letI : T2Space (TangentBundle I Yzero.M) := Yzero.t2TangentBundle
  letI : MetricSpace Yzero.M := (P (Lphi.φ 0)).ms
  have hbase : Yzero.basepoint ∈
      Lphi.hatSourceBall inp.decay P r 0 := by
    rw [NetLimitData.hatSourceBall, Metric.mem_closedBall, dist_self]
    exact hr
  obtain ⟨alphaZero, _zZero, _hzZero, _hclosedZero⟩ :=
    hbuffer 0 Yzero.basepoint hbase
  letI : Nonempty (LiveSlot L inp.pack r) := ⟨alphaZero⟩
  let etaMin : Real := Finset.univ.inf' Finset.univ_nonempty eta
  have hetaMin : 0 < etaMin := by
    dsimp only [etaMin]
    rw [Finset.lt_inf'_iff]
    intro alpha _halpha
    exact heta alpha
  let rho : Real := etaMin / 4
  have hrho : 0 < rho := div_pos hetaMin (by norm_num)
  refine ⟨rho, hrho, ?_⟩
  intro k
  dsimp only
  let Y := X.obj (Lphi.φ k)
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space Y.M := Y.t2
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  letI : MetricSpace Y.M := (P (Lphi.φ k)).ms
  intro y hy
  obtain ⟨alpha, z, hzy, hzclosed⟩ := hbuffer k y hy
  have hetaMinLe : etaMin ≤ eta alpha := by
    dsimp only [etaMin]
    exact Finset.inf'_le (s := Finset.univ) (f := eta) (by simp)
  have hsqrtTwo : Real.sqrt 2 < 2 := by nlinarith [Real.sq_sqrt (by norm_num : (0 : Real) ≤ 2)]
  have hrhoeta : Real.sqrt 2 * rho < eta alpha := by
    have hhalf : Real.sqrt 2 * rho < etaMin := by
      dsimp only [rho]
      have hsqrtNonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
      nlinarith
    exact hhalf.trans_le hetaMinLe
  obtain ⟨_hUopen, _hC0compact, _hC1compact, hC01, hC1U⟩ :=
    h.core_on inp P L r hr U C0 C1 aInf Jinf Jbarinf alpha
  have hC0U : C0 alpha ⊆ U alpha :=
    (hC01.trans interior_subset).trans hC1U
  obtain ⟨hUmetric, hUexp, _hUmap⟩ :=
    h.geom_on inp P L r hr U C0 C1 aInf Jinf Jbarinf k alpha
  let c : Y.M := seqCenterD inp.decay P Lphi k (alpha.1 : Nat)
  let chi := normalChartAt (I := I) Y.metric c
  have hequiv : NormalCoordMetricEquivOn (I := I) Y c (U alpha) := by
    intro w hw v
    exact inp.normalBounds.metric_equiv (Lphi.φ k) c w (hUmetric hw) v
  have hUtgt : U alpha ⊆ chi.target := by
    intro w hw
    have hnorm : ‖w‖ < expMapC2Radius (I := I) Y.metric c := by
      simpa only [Metric.mem_ball, dist_zero_right] using hUexp hw
    simpa only [chi] using
      ball_subset_normalChartAt_target (I := I) Y.metric c hnorm
  letI : RiemannianBundle (fun q : Y.M ↦ TangentSpace I q) := Y.riemBundle (I := I)
  have hcore := NormalCoordMetricEquivOn.ball_core_dist Y
    (hcomplete (Lphi.φ k)) (hconn (Lphi.φ k))
      (normal_enorm (I := I) Y) hequiv hC0U hUtgt
        (heta alpha) hzclosed hrhoeta
  have hcenter : chi.symm z = y := by
    simpa only [chi, c] using hzy
  have hpoint (x : Y.M) (hx : x ∈ Metric.ball y rho) :
      x ∈ chi.symm '' interior (C0 alpha) ∧
        dist (chi x) z ≤
          Real.sqrt 2 * inp.decay.dist (Lphi.φ k) x y := by
    have hxP : dist x y < rho := by
      simpa only [Metric.mem_ball] using hx
    have hdecay : inp.decay.dist (Lphi.φ k) x y < rho := by
      rw [← ProperMetricOn.dist_eq inp.decay inp.realizes P (Lphi.φ k) x y]
      exact hxP
    have hed : riemannianEDist I x y =
        ENNReal.ofReal (inp.decay.dist (Lphi.φ k) x y) := by
      have hrealize := inp.realizes.edist_eq (Lphi.φ k) x y
      simpa [PointedRiemannianManifold.emetricSpace] using hrealize
    have hriem : (riemannianEDist I (chi.symm z) x).toReal < rho := by
      rw [hcenter, riemannianEDist_comm, hed, ENNReal.toReal_ofReal
        (inp.realizes.dist_nonneg (Lphi.φ k) x y)]
      exact hdecay
    have hp := hcore hriem
    refine ⟨hp.1, ?_⟩
    have hcoord := hp.2
    rw [hcenter, riemannianEDist_comm, hed, ENNReal.toReal_ofReal
      (inp.realizes.dist_nonneg (Lphi.φ k) x y)] at hcoord
    simpa only [chi, c] using hcoord
  refine ⟨alpha, z, hcenter, ?_, ?_⟩
  · intro x hx
    exact (hpoint x hx).1
  · intro x hx
    exact (hpoint x hx).2

end HCGCompactness
end DifferentialGeometry
