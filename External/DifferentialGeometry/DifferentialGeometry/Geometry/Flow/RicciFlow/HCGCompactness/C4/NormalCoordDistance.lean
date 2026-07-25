import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepBInputs
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.GoodCoveringOrdered
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.H6IsometryDeriv
import DifferentialGeometry.Geometry.Comparison.GeodesicConvexity

set_option autoImplicit false









noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Bundle Manifold Set
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

variable {E : Type uE} [NormedAddCommGroup E]
variable [InnerProductSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in


omit [NeZero (Module.finrank Real E)] in
theorem H6Isometry.normalTrans_dist_le
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x y : Y.M)
    {U V : Set E}
    (hx : NormalCoordMetricEquivOn (I := I) Y x U)
    (hy : NormalCoordMetricEquivOn (I := I) Y y V) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    ∀ {u v : E},
      (∀ z ∈ segment Real u v,
        z ∈ (expMapDiffeo (I := I) Y.metric x).source) →
      (∀ z ∈ segment Real u v,
        expMapDiffeo (I := I) Y.metric x z ∈
          (normalChartAt (I := I) Y.metric y).source) →
      segment Real u v ⊆ U →
      Set.MapsTo (normalTransition (I := I) Y x y)
        (segment Real u v) V →
      dist (normalTransition (I := I) Y x y u)
          (normalTransition (I := I) Y x y v) ≤ 2 * dist u v := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  intro u v hsrc htgt hU hV
  let T := normalTransition (I := I) Y x y
  have hdiff : ∀ z ∈ segment Real u v, DifferentiableAt Real T z := by
    intro z hz
    have hdx : MDifferentiableAt 𝓘(Real, E) I
        (expMapDiffeo (I := I) Y.metric x) z :=
      ((expMapDiffeo (I := I) Y.metric x).contMDiffOn_toFun.mdifferentiableOn
        one_ne_zero z (hsrc z hz)).mdifferentiableAt
          ((expMapDiffeo (I := I) Y.metric x).open_source.mem_nhds (hsrc z hz))
    have hcy : MDifferentiableAt I 𝓘(Real, E)
        (normalChartAt (I := I) Y.metric y)
        (expMapDiffeo (I := I) Y.metric x z) :=
      ((normalChartAt (I := I) Y.metric y).contMDiffOn_toFun.mdifferentiableOn
        one_ne_zero _ (htgt z hz)).mdifferentiableAt
          ((normalChartAt (I := I) Y.metric y).open_source.mem_nhds (htgt z hz))
    exact mdifferentiableAt_iff_differentiableAt.mp
      (by simpa only [T, normalTransition] using hcy.comp z hdx)
  have hbound : ∀ z ∈ segment Real u v, ‖fderiv Real T z‖ ≤ 2 := by
    intro z hz
    exact H6Isometry.normal_fderiv_le_two (I := I) Y x y hx hy
      (hsrc z hz) (htgt z hz) (hU hz) (hV hz)
  have hmean := (convex_segment u v).norm_image_sub_le_of_norm_fderiv_le
    hdiff hbound (left_mem_segment Real u v) (right_mem_segment Real u v)
  calc
    dist (normalTransition (I := I) Y x y u)
        (normalTransition (I := I) Y x y v) =
        ‖T v - T u‖ := by rw [dist_eq_norm, norm_sub_rev]
    _ ≤ 2 * ‖v - u‖ := hmean
    _ = 2 * dist u v := by rw [← dist_eq_norm, dist_comm]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in



omit [NeZero (Module.finrank Real E)] in
theorem NormalCoordMetricEquivOn.symm_dist_le
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (P : ProperMetricOn (I := I) Y) {c : Y.M} {U : Set E}
    (h : NormalCoordMetricEquivOn (I := I) Y c U)
    (hUtgt :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      U ⊆ (normalChartAt (I := I) Y.metric c).target)
    {u v : E} (hseg : segment Real u v ⊆ U) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    letI : MetricSpace Y.M := P.ms
    dist ((normalChartAt (I := I) Y.metric c).symm u)
        ((normalChartAt (I := I) Y.metric c).symm v) ≤
      Real.sqrt 2 * dist u v := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  letI : MetricSpace Y.M := P.ms
  letI : RiemannianBundle (fun y : Y.M => TangentSpace I y) :=
    ⟨Y.metric.toRiemannianMetric⟩
  let e := expMapDiffeo (I := I) Y.metric c
  let eta := ContinuousAffineMap.lineMap (R := Real) u v
  let gamma : Real → Y.M := e ∘ eta
  have hetaU : MapsTo eta (Set.Icc (0 : Real) 1) U := by
    intro t ht
    apply hseg
    rw [segment_eq_image_lineMap]
    exact ⟨t, ht, rfl⟩
  have hetaSrc : MapsTo eta (Set.Icc (0 : Real) 1) e.source := by
    intro t ht
    simpa only [e, normalChartAt_target_eq] using hUtgt (hetaU ht)
  have hetaSmooth : ContMDiffOn 𝓘(Real, Real) 𝓘(Real, E) 1 eta (Set.Icc (0 : Real) 1) := by
    rw [contMDiffOn_iff_contDiffOn]
    exact eta.contDiff.contDiffOn
  have hgammaSmooth : ContMDiffOn 𝓘(Real, Real) I 1 gamma (Set.Icc (0 : Real) 1) :=
    e.contMDiffOn.comp hetaSmooth hetaSrc
  have hgammaZero : gamma 0 = e u := by
    simp only [gamma, Function.comp_apply, eta, ContinuousAffineMap.coe_lineMap_eq,
      AffineMap.lineMap_apply_zero]
  have hgammaOne : gamma 1 = e v := by
    simp only [gamma, Function.comp_apply, eta, ContinuousAffineMap.coe_lineMap_eq,
      AffineMap.lineMap_apply_one]
  have hpoint : ∀ t ∈ Set.Icc (0 : Real) 1,
      ‖mfderiv 𝓘(Real, Real) I gamma t 1‖ₑ ≤
        ENNReal.ofReal (Real.sqrt 2 * dist u v) := by
    intro t ht
    have heDiff : MDifferentiableAt 𝓘(Real, E) I e (eta t) :=
      e.mdifferentiableAt one_ne_zero (hetaSrc ht)
    have hetaDiff : MDifferentiableAt 𝓘(Real, Real) 𝓘(Real, E) eta t := by
      rw [mdifferentiableAt_iff_differentiableAt]
      exact eta.differentiableAt
    have hchain : mfderiv 𝓘(Real, Real) I gamma t 1 =
        mfderiv 𝓘(Real, E) I e (eta t)
          (mfderiv 𝓘(Real, Real) 𝓘(Real, E) eta t 1) := by
      rw [show gamma = e ∘ eta from rfl, mfderiv_comp t heDiff hetaDiff]
      rfl
    have hetaDeriv : mfderiv 𝓘(Real, Real) 𝓘(Real, E) eta t 1 = v - u := by
      rw [mfderiv_eq_fderiv]
      rw [eta.fderiv]
      change ((AffineMap.lineMap u v).linear : Real →ₗ[Real] E) 1 = v - u
      rw [AffineMap.lineMap_linear]
      simp
    rw [hchain, hetaDeriv, ← ofReal_norm_eq_enorm, norm_eq_sqrt_real_inner]
    refine ENNReal.ofReal_le_ofReal ?_
    have hub := (h (eta t) (hetaU ht) (v - u)).2
    calc
      Real.sqrt (Y.metric.inner (e (eta t))
          (mfderiv 𝓘(Real, E) I e (eta t) (v - u))
          (mfderiv 𝓘(Real, E) I e (eta t) (v - u)))
          = Real.sqrt (normalCoordMetric (I := I) Y c (eta t) (v - u) (v - u)) := by
              rw [normalCoordMetric_apply (I := I)]
      _ ≤ Real.sqrt (2 * ‖v - u‖ ^ 2) := Real.sqrt_le_sqrt hub
      _ = Real.sqrt 2 * dist u v := by
          rw [Real.sqrt_mul (by norm_num : (0 : Real) ≤ 2),
            Real.sqrt_sq (norm_nonneg (v - u)), dist_eq_norm]
          rw [norm_sub_rev]
  have hriem : Manifold.riemannianEDist I (e u) (e v) ≤
      ENNReal.ofReal (Real.sqrt 2 * dist u v) := by
    have hpath : Manifold.riemannianEDist I (e u) (e v) ≤
        Manifold.pathELength I gamma 0 1 :=
      Manifold.riemannianEDist_le_pathELength hgammaSmooth hgammaZero hgammaOne zero_le_one
    refine hpath.trans ?_
    rw [Manifold.pathELength_eq_lintegral_mfderiv_Icc]
    calc
      ∫⁻ t in Set.Icc (0 : Real) 1, ‖mfderiv 𝓘(Real, Real) I gamma t 1‖ₑ
          ≤ ∫⁻ _ in Set.Icc (0 : Real) 1,
              ENNReal.ofReal (Real.sqrt 2 * dist u v) :=
        MeasureTheory.setLIntegral_mono' measurableSet_Icc hpoint
      _ = ENNReal.ofReal (Real.sqrt 2 * dist u v) *
            MeasureTheory.volume (Set.Icc (0 : Real) 1) :=
        MeasureTheory.setLIntegral_const _ _
      _ = ENNReal.ofReal (Real.sqrt 2 * dist u v) := by
        rw [Real.volume_Icc]
        norm_num
  have hreal : Manifold.riemannianEDist I (e u) (e v) =
      ENNReal.ofReal (dist (e u) (e v)) := by
    have hp := P.realizes (e u) (e v)
    simpa [PointedRiemannianManifold.emetricSpace] using hp
  rw [hreal] at hriem
  have hdist : dist (e u) (e v) ≤ Real.sqrt 2 * dist u v :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hriem
  exact hdist

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in


theorem NormalCoordMetricEquivOn.chart_dist_le
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (hcomplete : MetricComplete (I := I) Y)
    (hconn :
      letI : TopologicalSpace Y.M := Y.topology
      ConnectedSpace Y.M)
    (hEnorm :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : RiemannianBundle (fun x : Y.M => TangentSpace I x) :=
        Y.riemBundle (I := I)
      ∀ (x : Y.M) (v : TangentSpace I x),
        ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (Y.metric.inner x v v)))
    {c : Y.M} {U : Set E}
    (h : NormalCoordMetricEquivOn (I := I) Y c U)
    {x y : Y.M}
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
      letI : RiemannianBundle (fun z : Y.M => TangentSpace I z) :=
        Y.riemBundle (I := I)
      letI : (z : Y.M) → InnerProductSpace Real (TangentSpace I z) :=
        Y.riemInner (I := I)
      letI : IsContinuousRiemannianBundle E
          (fun z : Y.M => TangentSpace I z) := Y.riemBundle_cont (I := I)
      letI : EMetricSpace Y.M := Y.emetricSpace (I := I)
      letI : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
      Set.MapsTo (minJoin (I := I) Y.metric hEnorm x y)
        (Set.Icc (0 : Real) 1)
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
    letI : RiemannianBundle (fun z : Y.M => TangentSpace I z) :=
      Y.riemBundle (I := I)
    letI : (z : Y.M) → InnerProductSpace Real (TangentSpace I z) :=
      Y.riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
        (fun z : Y.M => TangentSpace I z) := Y.riemBundle_cont (I := I)
    letI : EMetricSpace Y.M := Y.emetricSpace (I := I)
    letI : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
    dist (normalChartAt (I := I) Y.metric c x)
        (normalChartAt (I := I) Y.metric c y) ≤
      Real.sqrt 2 * (riemannianEDist I x y).toReal := by
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
  letI : RiemannianBundle (fun z : Y.M => TangentSpace I z) :=
    Y.riemBundle (I := I)
  letI : (z : Y.M) → InnerProductSpace Real (TangentSpace I z) :=
    Y.riemInner (I := I)
  letI : IsContinuousRiemannianBundle E
      (fun z : Y.M => TangentSpace I z) := Y.riemBundle_cont (I := I)
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
  have hdiff : ∀ t ∈ Set.Icc (0 : Real) 1,
      DifferentiableAt Real eta t := by
    intro t ht
    have hgammaDiff : MDifferentiableAt 𝓘(Real, Real) I gamma t := by
      have hs := intrinsicGeodesic_contMDiffOn
        (I := I) Y.metric hEnorm x w
      have hm := hs.mdifferentiableOn one_ne_zero t (Set.mem_univ t)
      simpa only [gamma, minJoin, w] using
        hm.mdifferentiableAt (isOpen_univ.mem_nhds (Set.mem_univ t))
    have hchiDiff : MDifferentiableAt I 𝓘(Real, E) chi (gamma t) :=
      (chi.contMDiffOn_toFun.mdifferentiableOn one_ne_zero _
        (hjoin ht).1).mdifferentiableAt
          (chi.open_source.mem_nhds (hjoin ht).1)
    exact mdifferentiableAt_iff_differentiableAt.mp
      (by simpa only [eta] using hchiDiff.comp t hgammaDiff)
  have hbound : ∀ t ∈ Set.Icc (0 : Real) 1,
      ‖deriv eta t‖ ≤ Real.sqrt 2 * d := by
    intro t ht
    have hgammaDiff : MDifferentiableAt 𝓘(Real, Real) I gamma t := by
      have hs := intrinsicGeodesic_contMDiffOn
        (I := I) Y.metric hEnorm x w
      have hm := hs.mdifferentiableOn one_ne_zero t (Set.mem_univ t)
      simpa only [gamma, minJoin, w] using
        hm.mdifferentiableAt (isOpen_univ.mem_nhds (Set.mem_univ t))
    have hchiDiff : MDifferentiableAt I 𝓘(Real, E) chi (gamma t) :=
      (chi.contMDiffOn_toFun.mdifferentiableOn one_ne_zero _
        (hjoin ht).1).mdifferentiableAt
          (chi.open_source.mem_nhds (hjoin ht).1)
    have hetaDiff : MDifferentiableAt 𝓘(Real, Real) 𝓘(Real, E) eta t := by
      simpa only [eta] using hchiDiff.comp t hgammaDiff
    have hetaSrc : eta t ∈ e.source := by
      rw [← normalChartAt_target_eq (I := I)]
      exact chi.map_source (hjoin ht).1
    have heDiff : MDifferentiableAt 𝓘(Real, E) I e (eta t) :=
      (e.contMDiffOn_toFun.mdifferentiableOn one_ne_zero _ hetaSrc).mdifferentiableAt
        (e.open_source.mem_nhds hetaSrc)
    have hnear : ∀ᶠ s in nhds t, gamma s ∈ chi.source :=
      hgammaCont.continuousAt.eventually (chi.open_source.mem_nhds (hjoin ht).1)
    have heq : e ∘ eta =ᶠ[nhds t] gamma := by
      filter_upwards [hnear] with s hs
      change chi.symm (chi (gamma s)) = gamma s
      exact chi.left_inv hs
    have hcomp :
        (mfderiv 𝓘(Real, E) I e (eta t)).comp
            (mfderiv 𝓘(Real, Real) 𝓘(Real, E) eta t) =
          mfderiv 𝓘(Real, Real) I gamma t := by
      have hderiv := Filter.EventuallyEq.mfderiv_eq
        (I := 𝓘(Real, Real)) (I' := I) heq
      rw [mfderiv_comp t heDiff hetaDiff] at hderiv
      simpa only using hderiv
    have hetaVel : mfderiv 𝓘(Real, Real) 𝓘(Real, E) eta t 1 =
        deriv eta t := by
      rw [mfderiv_eq_fderiv]
      exact fderiv_apply_one_eq_deriv
    have hvel : mfderiv 𝓘(Real, E) I e (eta t) (deriv eta t) =
        mfderiv 𝓘(Real, Real) I gamma t 1 := by
      have hv := DFunLike.congr_fun hcomp (1 : Real)
      change (mfderiv 𝓘(Real, E) I e (eta t))
          (mfderiv 𝓘(Real, Real) 𝓘(Real, E) eta t 1) =
        mfderiv 𝓘(Real, Real) I gamma t 1 at hv
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
    have hspeed : Y.metric.inner (gamma t)
          (mfderiv 𝓘(Real, Real) I gamma t 1)
          (mfderiv 𝓘(Real, Real) I gamma t 1) = d ^ 2 := by
      calc
        _ = Y.metric.inner x w w := by
          simpa only [gamma, minJoin, w] using
            intrinsicGeodesic_speedSq_eq (I := I) Y.metric hEnorm x w t
        _ = d ^ 2 := hlaunch
    have hbase : e (eta t) = gamma t := by
      exact heq.self_of_nhds
    have hmetric : normalCoordMetric (I := I) Y c (eta t)
          (deriv eta t) (deriv eta t) = d ^ 2 := by
      rw [normalCoordMetric_apply (I := I), hbase]
      change Y.metric.inner (gamma t)
          (mfderiv 𝓘(Real, E) I e (eta t) (deriv eta t))
          (mfderiv 𝓘(Real, E) I e (eta t) (deriv eta t)) = d ^ 2
      rw [hvel]
      exact hspeed
    have hlower := (h (eta t) (hjoin ht).2 (deriv eta t)).1
    rw [hmetric] at hlower
    have hsq : ‖deriv eta t‖ ^ 2 ≤
        (Real.sqrt 2 * d) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : Real) ≤ 2)]
      nlinarith
    exact le_of_sq_le_sq hsq (mul_nonneg (Real.sqrt_nonneg 2) hd)
  have hmean := Convex.norm_image_sub_le_of_norm_deriv_le
    (f := eta) hdiff hbound (convex_Icc (0 : Real) 1)
    (left_mem_Icc.mpr zero_le_one) (right_mem_Icc.mpr zero_le_one)
  have hend : dist (chi x) (chi y) = ‖eta 1 - eta 0‖ := by
    simp only [eta, gamma, Function.comp_apply, minJoin_zero, minJoin_one,
      dist_eq_norm, norm_sub_rev]
  rw [hend]
  norm_num at hmean
  simpa only [d] using hmean

end HCGCompactness
end DifferentialGeometry

end
