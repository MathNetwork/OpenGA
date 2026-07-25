import DifferentialGeometry.Geometry.Coordinates.TangentPartialDiffeomorph
import DifferentialGeometry.Geometry.Exponential.DiagInvReadout
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.NormalMetricExtend
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.NormalDiagAt
import Mathlib.Topology.OpenPartialHomeomorph.Composition

set_option autoImplicit false









noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Bundle Manifold Set TopologicalSpace
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]



noncomputable def normalTanHome
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : IsManifold I 1 Y.M := IsManifold.of_le
      (I := I) (M := Y.M) (n := ∞) (by decide)
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    OpenPartialHomeomorph (E × E) (TangentBundle I Y.M) := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : IsManifold I 1 Y.M := IsManifold.of_le
    (I := I) (M := Y.M) (n := ∞) (by decide)
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  exact
    (tangentBundleModelSpaceHomeomorph 𝓘(Real, E)).symm.toOpenPartialHomeomorph.trans
      (PartialDiffeomorph.tangentHome (normalExpPD (I := I) Y x) (by simp))



noncomputable def normalPairHome
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    OpenPartialHomeomorph (E × E) (Y.M × Y.M) := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  exact (normalExpPD (I := I) Y x).toOpenPartialHomeomorph.prod
    (normalExpPD (I := I) Y x).toOpenPartialHomeomorph



theorem normalTanHome_apply
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M)
    (z : E × E) (hz : z.1 ∈ normalBall (I := I) Y x) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : IsManifold I 1 Y.M := IsManifold.of_le
      (I := I) (M := Y.M) (n := ∞) (by decide)
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    normalTanHome (I := I) Y x z = normalTangent (I := I) Y x z := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : IsManifold I 1 Y.M := IsManifold.of_le
    (I := I) (M := Y.M) (n := ∞) (by decide)
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  change tangentMapWithin 𝓘(Real, E) I
      (normalExpPD (I := I) Y x : E → Y.M)
      (normalExpPD (I := I) Y x).source
      ((tangentBundleModelSpaceHomeomorph 𝓘(Real, E)).symm z) =
    normalTangent (I := I) Y x z
  have huniq : UniqueMDiffWithinAt 𝓘(Real, E)
      (normalExpPD (I := I) Y x).source z.1 :=
    (normalExpPD (I := I) Y x).open_source.uniqueMDiffOn z.1 (by
      simpa only [normalExpPD_source] using hz)
  have hdiff : MDifferentiableAt 𝓘(Real, E) I
      (normalExpPD (I := I) Y x : E → Y.M) z.1 :=
    (normalExpPD (I := I) Y x).mdifferentiableAt (by simp) (by
      simpa only [normalExpPD_source] using hz)
  rw [tangentMapWithin_eq_tangentMap huniq hdiff]
  rfl


theorem normalPairHome_apply
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M)
    (z : E × E) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    normalPairHome (I := I) Y x z = normalPair (I := I) Y x z := by
  rfl



theorem normalTanHome_source
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : IsManifold I 1 Y.M := IsManifold.of_le
      (I := I) (M := Y.M) (n := ∞) (by decide)
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    (normalTanHome (I := I) Y x).source =
      Prod.fst ⁻¹' (normalBall (I := I) Y x : Set E) := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : IsManifold I 1 Y.M := IsManifold.of_le
    (I := I) (M := Y.M) (n := ∞) (by decide)
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  ext z
  simp only [normalTanHome, OpenPartialHomeomorph.trans_source,
    Homeomorph.toOpenPartialHomeomorph_source,
    PartialDiffeomorph.tangentHome, normalExpPD_source]
  constructor
  · rintro ⟨_, hz⟩
    exact hz
  · intro hz
    exact ⟨mem_univ z, hz⟩



theorem normalPair_source
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    (normalPairHome (I := I) Y x).source =
      (normalBall (I := I) Y x : Set E) ×ˢ
        (normalBall (I := I) Y x : Set E) := by
  rfl



noncomputable def normalDiagHome
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M)
    (e : OpenPartialHomeomorph (E × E) (E × E)) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : IsManifold I 1 Y.M := IsManifold.of_le
      (I := I) (M := Y.M) (n := ∞) (by decide)
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    OpenPartialHomeomorph (TangentBundle I Y.M) (Y.M × Y.M) := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : IsManifold I 1 Y.M := IsManifold.of_le
    (I := I) (M := Y.M) (n := ∞) (by decide)
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  exact (normalTanHome (I := I) Y x).symm.trans
    (e.trans (normalPairHome (I := I) Y x))

private theorem pair_mem_target
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (A : OpenPartialHomeomorph X Y) (e : OpenPartialHomeomorph X X)
    (P : OpenPartialHomeomorph X Z) {w : X}
    (hwP : w ∈ P.source) (hwe : w ∈ e.target) (hwA : e.symm w ∈ A.source) :
    P w ∈ (A.symm.trans (e.trans P)).target := by
  rw [OpenPartialHomeomorph.trans_target]
  constructor
  · rw [OpenPartialHomeomorph.trans_target]
    refine ⟨P.map_source hwP, ?_⟩
    change P.symm (P w) ∈ e.target
    rw [P.left_inv hwP]
    exact hwe
  · change e.symm (P.symm (P w)) ∈ A.source
    rw [P.left_inv hwP]
    exact hwA


theorem normalTanHome_inf
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : IsManifold I 1 Y.M := IsManifold.of_le
      (I := I) (M := Y.M) (n := ∞) (by decide)
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    ContMDiffOn 𝓘(Real, E × E) I.tangent ∞
      (normalTanHome (I := I) Y x) (normalTanHome (I := I) Y x).source := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : IsManifold I 1 Y.M := IsManifold.of_le
    (I := I) (M := Y.M) (n := ∞) (by decide)
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  let Φ := normalExpPD (I := I) Y x
  let m : OpenPartialHomeomorph (E × E) (TangentBundle 𝓘(Real, E) E) :=
    (tangentBundleModelSpaceHomeomorph 𝓘(Real, E)).symm.toOpenPartialHomeomorph
  let t := PartialDiffeomorph.tangentHome Φ (by simp)
  have hm : ContMDiff (𝓘(Real, E).prod 𝓘(Real, E)) 𝓘(Real, E).tangent ∞
      (m : E × E → TangentBundle 𝓘(Real, E) E) := by
    have hm0 := contMDiff_tangentBundleModelSpaceHomeomorph_symm
      (I := 𝓘(Real, E)) (n := (∞ : WithTop ℕ∞))
    unfold ModelProd at hm0
    rw [← chartedSpaceSelf_prod] at hm0
    simpa only [m] using hm0
  have ht : ContMDiffOn 𝓘(Real, E).tangent I.tangent ∞
      (t : TangentBundle 𝓘(Real, E) E → TangentBundle I Y.M) t.source := by
    simpa only [t, PartialDiffeomorph.tangentHome] using
      Φ.contMDiffOn_toFun.contMDiffOn_tangentMapWithin
        (m := (∞ : WithTop ℕ∞)) (by simp) Φ.open_source.uniqueMDiffOn
  have hmOn : ContMDiffOn (𝓘(Real, E).prod 𝓘(Real, E))
      𝓘(Real, E).tangent ∞ (m : E × E → TangentBundle 𝓘(Real, E) E) m.source :=
    hm.contMDiffOn
  change ContMDiffOn (𝓘(Real, E).prod 𝓘(Real, E)) I.tangent ∞
    ((t : TangentBundle 𝓘(Real, E) E → TangentBundle I Y.M) ∘
      (m : E × E → TangentBundle 𝓘(Real, E) E))
    (m.source ∩ (m : E × E → TangentBundle 𝓘(Real, E) E) ⁻¹' t.source)
  exact ht.comp' hmOn



theorem normalTan_inv_inf
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : IsManifold I 1 Y.M := IsManifold.of_le
      (I := I) (M := Y.M) (n := ∞) (by decide)
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    ContMDiffOn I.tangent 𝓘(Real, E × E) ∞
      (normalTanHome (I := I) Y x).symm
      (normalTanHome (I := I) Y x).target := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : IsManifold I 1 Y.M := IsManifold.of_le
    (I := I) (M := Y.M) (n := ∞) (by decide)
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  let Φ := normalExpPD (I := I) Y x
  let m : OpenPartialHomeomorph (E × E) (TangentBundle 𝓘(Real, E) E) :=
    (tangentBundleModelSpaceHomeomorph 𝓘(Real, E)).symm.toOpenPartialHomeomorph
  let t := PartialDiffeomorph.tangentHome Φ (by simp)
  have hm : ContMDiff 𝓘(Real, E).tangent
      (𝓘(Real, E).prod 𝓘(Real, E)) ∞
      (m.symm : TangentBundle 𝓘(Real, E) E → E × E) := by
    have hm0 := contMDiff_tangentBundleModelSpaceHomeomorph
      (I := 𝓘(Real, E)) (n := (∞ : WithTop ℕ∞))
    unfold ModelProd at hm0
    rw [← chartedSpaceSelf_prod] at hm0
    simpa only [m] using hm0
  have ht : ContMDiffOn I.tangent 𝓘(Real, E).tangent ∞
      (t.symm : TangentBundle I Y.M → TangentBundle 𝓘(Real, E) E) t.target := by
    simpa only [t, PartialDiffeomorph.tangentHome] using
      Φ.contMDiffOn_invFun.contMDiffOn_tangentMapWithin
        (m := (∞ : WithTop ℕ∞)) (by simp) Φ.open_target.uniqueMDiffOn
  have hmOn : ContMDiffOn 𝓘(Real, E).tangent
      (𝓘(Real, E).prod 𝓘(Real, E)) ∞
      (m.symm : TangentBundle 𝓘(Real, E) E → E × E) m.target :=
    hm.contMDiffOn
  change ContMDiffOn I.tangent (𝓘(Real, E).prod 𝓘(Real, E)) ∞
    ((m.symm : TangentBundle 𝓘(Real, E) E → E × E) ∘
      (t.symm : TangentBundle I Y.M → TangentBundle 𝓘(Real, E) E))
    (t.target ∩
      (t.symm : TangentBundle I Y.M → TangentBundle 𝓘(Real, E) E) ⁻¹' m.target)
  exact hmOn.comp' ht


theorem normalPairHome_inf
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    ContMDiffOn 𝓘(Real, E × E) (I.prod I) ∞
      (normalPairHome (I := I) Y x) (normalPairHome (I := I) Y x).source := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  have h := (normalExpPD (I := I) Y x).contMDiffOn_toFun.prodMap
    (normalExpPD (I := I) Y x).contMDiffOn_toFun
  simpa only [normalPairHome, OpenPartialHomeomorph.prod_source,
    OpenPartialHomeomorph.prod_apply] using h



theorem normalPair_inv_inf
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    ContMDiffOn (I.prod I) 𝓘(Real, E × E) ∞
      (normalPairHome (I := I) Y x).symm
      (normalPairHome (I := I) Y x).target := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  have h := (normalExpPD (I := I) Y x).contMDiffOn_invFun.prodMap
    (normalExpPD (I := I) Y x).contMDiffOn_invFun
  simpa only [normalPairHome, OpenPartialHomeomorph.prod_target,
    OpenPartialHomeomorph.prod_symm_apply] using h

namespace NormalCoordMetricBoundInput



theorem chart_mem_norm_le
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (h : NormalCoordMetricBoundInput (I := I) X)
    (k : Nat) (c y : (X.obj k).M)
    (hdist :
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
      letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
      letI : T2Space (X.obj k).M := (X.obj k).t2
      letI : T2Space (TangentBundle I (X.obj k).M) :=
        (X.obj k).t2TangentBundle
      letI : RiemannianBundle
          (fun z : (X.obj k).M ↦ TangentSpace I z) :=
        (X.obj k).riemBundle (I := I)
      letI : IsContinuousRiemannianBundle E
          (fun z : (X.obj k).M ↦ TangentSpace I z) :=
        (X.obj k).riemBundle_cont (I := I)
      letI : EMetricSpace (X.obj k).M := (X.obj k).emetricSpace (I := I)
      riemannianEDist I c y ≠ ⊤ ∧
        (riemannianEDist I c y).toReal <
          expRadiusGp (I := I) (X.obj k).metric c) :
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
    letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    letI : T2Space (X.obj k).M := (X.obj k).t2
    letI : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    letI : RiemannianBundle
        (fun z : (X.obj k).M ↦ TangentSpace I z) :=
      (X.obj k).riemBundle (I := I)
    letI : IsContinuousRiemannianBundle E
        (fun z : (X.obj k).M ↦ TangentSpace I z) :=
      (X.obj k).riemBundle_cont (I := I)
    letI : EMetricSpace (X.obj k).M := (X.obj k).emetricSpace (I := I)
    y ∈ (NormalCoordinates.normalChartAt (I := I) (X.obj k).metric c).source ∧
      ‖NormalCoordinates.normalChartAt (I := I) (X.obj k).metric c y‖ ≤
        2 * (riemannianEDist I c y).toReal := by
  letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
  letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
  letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  letI : T2Space (X.obj k).M := (X.obj k).t2
  letI : T2Space (TangentBundle I (X.obj k).M) :=
    (X.obj k).t2TangentBundle
  letI : RiemannianBundle (fun z : (X.obj k).M ↦ TangentSpace I z) :=
    (X.obj k).riemBundle (I := I)
  letI : IsContinuousRiemannianBundle E
      (fun z : (X.obj k).M ↦ TangentSpace I z) :=
    (X.obj k).riemBundle_cont (I := I)
  letI : EMetricSpace (X.obj k).M := (X.obj k).emetricSpace (I := I)
  obtain ⟨v, hvTarget, _hvDomain, hvLength, hyExp⟩ :=
    metricBall_subset_normalBall (I := I) (X.obj k).metric c
      (normal_enorm (I := I) (X.obj k)) hdist.1 hdist.2
  have hySource :
      y ∈ (NormalCoordinates.normalChartAt (I := I) (X.obj k).metric c).source :=
    memNChartSrcOfDist (I := I) (X.obj k).metric c
      (normal_enorm (I := I) (X.obj k)) hdist.1 hdist.2
  have hchart :
      NormalCoordinates.normalChartAt (I := I) (X.obj k).metric c y = v := by
    have hsymm :
        (NormalCoordinates.normalChartAt (I := I) (X.obj k).metric c).symm v = y := by
      rw [NormalCoordinates.normalChartAt_symm_apply (I := I) (X.obj k).metric c hvTarget]
      exact hyExp.symm
    rw [← hsymm]
    exact (NormalCoordinates.normalChartAt (I := I) (X.obj k).metric c).right_inv hvTarget
  have hzero : (0 : E) ∈ Metric.ball 0 (h.radius k c) := by
    rw [Metric.mem_ball, dist_self]
    exact h.radius_pos k c
  have hcoercive := (h.metric_equiv k c 0 hzero v).1
  have hmetricZero :
      normalCoordMetric (I := I) (X.obj k) c 0 v v =
        (X.obj k).metric.inner c v v := by
    rw [normalCoordMetric_apply (I := I),
      NormalCoordinates.expMapDiffeo_zero (I := I)]
    exact NormalCoordinates.normalChartAt_metric_pullback_at_origin
      (I := I) (X.obj k).metric c v v
  rw [hmetricZero] at hcoercive
  have hinnerNonneg : 0 ≤ (X.obj k).metric.inner c v v := by
    exact (mul_nonneg (by norm_num) (sq_nonneg ‖v‖)).trans hcoercive
  have hinnerEq :
      (X.obj k).metric.inner c v v = (riemannianEDist I c y).toReal ^ 2 := by
    calc
      (X.obj k).metric.inner c v v =
          Real.sqrt ((X.obj k).metric.inner c v v) ^ 2 :=
        (Real.sq_sqrt hinnerNonneg).symm
      _ = (riemannianEDist I c y).toReal ^ 2 := congrArg (fun t : Real => t ^ 2) hvLength
  rw [hinnerEq] at hcoercive
  rw [hchart]
  refine ⟨hySource, ?_⟩
  have hdistNonneg : 0 ≤ (riemannianEDist I c y).toReal := ENNReal.toReal_nonneg
  by_contra hle
  have hlt : 2 * (riemannianEDist I c y).toReal < ‖v‖ := lt_of_not_ge hle
  have hsq : (2 * (riemannianEDist I c y).toReal) ^ 2 < ‖v‖ ^ 2 :=
    (sq_lt_sq₀ (mul_nonneg (by norm_num) hdistNonneg) (norm_nonneg v)).2 hlt
  nlinarith

end NormalCoordMetricBoundInput

namespace IsNormalDiag



theorem eqOnSource
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (hcomplete : MetricComplete (I := I) Y)
    (hconn : letI : TopologicalSpace Y.M := Y.topology; ConnectedSpace Y.M)
    (x : Y.M) {q : NNReal} {δ δ' : Real}
    {e e' : OpenPartialHomeomorph (E × E) (E × E)}
    (h : IsNormalDiag (I := I) Y hcomplete hconn x q δ e)
    (hf : NormalDiagFence (I := I) Y x q e)
    (h' : IsNormalDiag (I := I) Y hcomplete hconn x q δ' e')
    (hf' : NormalDiagFence (I := I) Y x q e') :
    e ≈ e' := by
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
  letI : RiemannianBundle (fun y : Y.M ↦ TangentSpace I y) :=
    Y.riemBundle (I := I)
  letI : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
    Y.riemInner (I := I)
  letI : IsContinuousRiemannianBundle E
      (fun y : Y.M ↦ TangentSpace I y) := Y.riemBundle_cont (I := I)
  letI : EMetricSpace Y.M := Y.emetricSpace (I := I)
  letI : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
  change e.source = Metric.ball (0 : E × E) q ∧
    e 0 = 0 ∧
    ContDiffOn Real ∞ (e : E × E → E × E) e.source ∧
    Metric.closedBall (0 : E × E) δ ⊆ e.target ∧
    ContDiffOn Real ∞ e.symm e.target ∧
    ∀ z ∈ Metric.closedBall (0 : E × E) q,
      normalPair (I := I) Y x (e z) =
        diagExp (I := I) Y.metric (normal_enorm (I := I) Y)
          (normalTangent (I := I) Y x z) at h
  change e'.source = Metric.ball (0 : E × E) q ∧
    e' 0 = 0 ∧
    ContDiffOn Real ∞ (e' : E × E → E × E) e'.source ∧
    Metric.closedBall (0 : E × E) δ' ⊆ e'.target ∧
    ContDiffOn Real ∞ e'.symm e'.target ∧
    ∀ z ∈ Metric.closedBall (0 : E × E) q,
      normalPair (I := I) Y x (e' z) =
        diagExp (I := I) Y.metric (normal_enorm (I := I) Y)
          (normalTangent (I := I) Y x z) at h'
  change ∀ z ∈ Metric.closedBall (0 : E × E) q,
    z.1 ∈ normalBall (I := I) Y x ∧
    (e z).1 ∈ normalBall (I := I) Y x ∧
    (e z).2 ∈ normalBall (I := I) Y x at hf
  change ∀ z ∈ Metric.closedBall (0 : E × E) q,
    z.1 ∈ normalBall (I := I) Y x ∧
    (e' z).1 ∈ normalBall (I := I) Y x ∧
    (e' z).2 ∈ normalBall (I := I) Y x at hf'
  rcases h with ⟨hsource, _, _, _, _, hdiag⟩
  rcases h' with ⟨hsource', _, _, _, _, hdiag'⟩
  refine ⟨hsource.trans hsource'.symm, ?_⟩
  intro z hz
  have hzBall : z ∈ Metric.ball (0 : E × E) q := by
    rwa [← hsource]
  have hzClosed : z ∈ Metric.closedBall (0 : E × E) q :=
    Metric.ball_subset_closedBall hzBall
  have hzFence := hf z hzClosed
  have hzFence' := hf' z hzClosed
  apply (normalPairHome (I := I) Y x).injOn
  · change e z ∈ (normalPairHome (I := I) Y x).source
    rw [normalPair_source]
    exact ⟨hzFence.2.1, hzFence.2.2⟩
  · change e' z ∈ (normalPairHome (I := I) Y x).source
    rw [normalPair_source]
    exact ⟨hzFence'.2.1, hzFence'.2.2⟩
  · rw [normalPairHome_apply, normalPairHome_apply]
    exact (hdiag z hzClosed).trans (hdiag' z hzClosed).symm



noncomputable def toBranch
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (hcomplete : MetricComplete (I := I) Y)
    (hconn : letI : TopologicalSpace Y.M := Y.topology; ConnectedSpace Y.M)
    (x : Y.M) {q : NNReal} {δ : Real}
    {e : OpenPartialHomeomorph (E × E) (E × E)}
    (hq : 0 < q) (h : IsNormalDiag (I := I) Y hcomplete hconn x q δ e) :
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
    letI : RiemannianBundle (fun y : Y.M => TangentSpace I y) :=
      Y.riemBundle (I := I)
    letI : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
      Y.riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
      (fun y : Y.M => TangentSpace I y) := Y.riemBundle_cont (I := I)
    letI : EMetricSpace Y.M := Y.emetricSpace (I := I)
    letI : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
    DiagInvBranch (I := I) Y.metric (normal_enorm (I := I) Y) x := by
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
  letI : RiemannianBundle (fun y : Y.M => TangentSpace I y) :=
    Y.riemBundle (I := I)
  letI : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
    Y.riemInner (I := I)
  letI : IsContinuousRiemannianBundle E
      (fun y : Y.M => TangentSpace I y) := Y.riemBundle_cont (I := I)
  letI : EMetricSpace Y.M := Y.emetricSpace (I := I)
  letI : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
  have hdata := h
  change e.source = Metric.ball (0 : E × E) q ∧
    e 0 = 0 ∧
    ContDiffOn Real ∞ (e : E × E → E × E) e.source ∧
    Metric.closedBall (0 : E × E) δ ⊆ e.target ∧
    ContDiffOn Real ∞ e.symm e.target ∧
    ∀ z ∈ Metric.closedBall (0 : E × E) q,
      normalPair (I := I) Y x (e z) =
        diagExp (I := I) Y.metric (normal_enorm (I := I) Y)
          (normalTangent (I := I) Y x z) at h
  rcases h with ⟨hsource, hzero, _heInf, _htarget, hinvInf, hdiag⟩
  let A := normalTanHome (I := I) Y x
  let P := normalPairHome (I := I) Y x
  let D := normalDiagHome (I := I) Y x e
  let u0 : TangentBundle I Y.M := ⟨x, (0 : TangentSpace I x)⟩
  have hzNormal : (0 : E) ∈ normalBall (I := I) Y x := by
    change dist (0 : E) 0 < expMapC2Radius (I := I) Y.metric x
    simpa only [dist_self] using expMapC2Radius_pos (I := I) Y.metric x
  have hA0src : (0 : E × E) ∈ A.source := by
    change (0 : E × E) ∈ (normalTanHome (I := I) Y x).source
    rw [normalTanHome_source]
    exact hzNormal
  have hA0 : A 0 = u0 := by
    change normalTanHome (I := I) Y x 0 = u0
    rw [normalTanHome_apply (I := I) Y x 0 hzNormal]
    simp only [normalTangent, u0, Prod.fst_zero, Prod.snd_zero]
    rw [NormalCoordinates.expMapDiffeo_zero]
    apply TotalSpace.mk_inj.mpr
    change (mfderiv 𝓘(Real, E) I
      (fun v : E => NormalCoordinates.expMapDiffeo (I := I) Y.metric x v) 0) 0 =
        (0 : E)
    exact ContinuousLinearMap.map_zero _
  have hP0src : (0 : E × E) ∈ P.source := by
    change (0 : E × E) ∈ (normalPairHome (I := I) Y x).source
    rw [normalPair_source]
    exact ⟨hzNormal, hzNormal⟩
  refine
    { hom := D
      zero_mem := ?_
      hom_eq := ?_
      inv_inf := ?_ }
  · change u0 ∈ D.source
    change u0 ∈ (A.symm.trans (e.trans P)).source
    rw [OpenPartialHomeomorph.trans_source]
    constructor
    · change u0 ∈ A.target
      rw [← hA0]
      exact A.map_source hA0src
    · change A.symm u0 ∈ (e.trans P).source
      have hAinv0 : A.symm u0 = 0 := by
        rw [← hA0]
        exact A.left_inv hA0src
      rw [hAinv0, OpenPartialHomeomorph.trans_source]
      constructor
      · rw [hsource]
        exact Metric.mem_ball_self (by exact_mod_cast hq)
      · change e 0 ∈ P.source
        rw [hzero]
        exact hP0src
  · intro u hu
    change u ∈ (A.symm.trans (e.trans P)).source at hu
    rw [OpenPartialHomeomorph.trans_source] at hu
    rcases hu with ⟨huA, huRest⟩
    change A.symm u ∈ (e.trans P).source at huRest
    rw [OpenPartialHomeomorph.trans_source] at huRest
    rcases huRest with ⟨hze, _hzP⟩
    let z : E × E := A.symm u
    have hzA : z ∈ A.source := A.map_target huA
    have hzNormal' : z.1 ∈ normalBall (I := I) Y x := by
      have hzA' : z ∈ (normalTanHome (I := I) Y x).source := hzA
      rw [normalTanHome_source] at hzA'
      exact hzA'
    have hztan : normalTangent (I := I) Y x z = u := by
      calc
        normalTangent (I := I) Y x z = A z :=
          (normalTanHome_apply (I := I) Y x z hzNormal').symm
        _ = u := A.right_inv huA
    have hzBall : z ∈ Metric.ball (0 : E × E) q := by
      rw [← hsource]
      exact hze
    have hzClosed : z ∈ Metric.closedBall (0 : E × E) q :=
      Metric.ball_subset_closedBall hzBall
    calc
      D u = P (e z) := rfl
      _ = normalPair (I := I) Y x (e z) := normalPairHome_apply (I := I) Y x (e z)
      _ = diagExp (I := I) Y.metric (normal_enorm (I := I) Y)
          (normalTangent (I := I) Y x z) := hdiag z hzClosed
      _ = diagExp (I := I) Y.metric (normal_enorm (I := I) Y) u :=
        congrArg (diagExp (I := I) Y.metric (normal_enorm (I := I) Y)) hztan
  · let B := e.trans P
    have hPInv : ContMDiffOn (I.prod I) 𝓘(Real, E × E) ∞
        P.symm P.target := normalPair_inv_inf (I := I) Y x
    have heInv : ContMDiffOn 𝓘(Real, E × E) 𝓘(Real, E × E) ∞
        e.symm e.target := hinvInf.contMDiffOn
    have hBInv : ContMDiffOn (I.prod I) 𝓘(Real, E × E) ∞
        B.symm B.target := by
      change ContMDiffOn (I.prod I) 𝓘(Real, E × E) ∞
        ((e.symm : E × E → E × E) ∘ (P.symm : Y.M × Y.M → E × E))
        (P.target ∩ (P.symm : Y.M × Y.M → E × E) ⁻¹' e.target)
      exact heInv.comp' hPInv
    have hAInf : ContMDiffOn 𝓘(Real, E × E) I.tangent ∞ A A.source :=
      normalTanHome_inf (I := I) Y x
    change ContMDiffOn (I.prod I) I.tangent ∞
      ((A : E × E → TangentBundle I Y.M) ∘ (B.symm : Y.M × Y.M → E × E))
      (B.target ∩ (B.symm : Y.M × Y.M → E × E) ⁻¹' A.source)
    exact hAInf.comp' hBInv



@[simp] theorem toBranch_hom
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (hcomplete : MetricComplete (I := I) Y)
    (hconn : letI : TopologicalSpace Y.M := Y.topology; ConnectedSpace Y.M)
    (x : Y.M) {q : NNReal} {δ : Real}
    {e : OpenPartialHomeomorph (E × E) (E × E)}
    (hq : 0 < q) (h : IsNormalDiag (I := I) Y hcomplete hconn x q δ e) :
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
    letI : RiemannianBundle (fun y : Y.M ↦ TangentSpace I y) :=
      Y.riemBundle (I := I)
    letI : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
      Y.riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
      (fun y : Y.M ↦ TangentSpace I y) := Y.riemBundle_cont (I := I)
    letI : EMetricSpace Y.M := Y.emetricSpace (I := I)
    letI : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
    (toBranch (I := I) Y hcomplete hconn x hq h).hom =
      normalDiagHome (I := I) Y x e := by
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
  letI : RiemannianBundle (fun y : Y.M ↦ TangentSpace I y) :=
    Y.riemBundle (I := I)
  letI : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
    Y.riemInner (I := I)
  letI : IsContinuousRiemannianBundle E
      (fun y : Y.M ↦ TangentSpace I y) := Y.riemBundle_cont (I := I)
  letI : EMetricSpace Y.M := Y.emetricSpace (I := I)
  letI : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
  change e.source = Metric.ball (0 : E × E) q ∧
    e 0 = 0 ∧
    ContDiffOn Real ∞ (e : E × E → E × E) e.source ∧
    Metric.closedBall (0 : E × E) δ ⊆ e.target ∧
    ContDiffOn Real ∞ e.symm e.target ∧
    ∀ z ∈ Metric.closedBall (0 : E × E) q,
      normalPair (I := I) Y x (e z) =
        diagExp (I := I) Y.metric (normal_enorm (I := I) Y)
          (normalTangent (I := I) Y x z) at h
  rcases h with ⟨_, _, _, _, _, _⟩
  rfl



theorem full_transport
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (hcomplete : MetricComplete (I := I) Y)
    (hconn : letI : TopologicalSpace Y.M := Y.topology; ConnectedSpace Y.M)
    (x : Y.M) {q : NNReal} {δ : Real}
    {e : OpenPartialHomeomorph (E × E) (E × E)}
    (hq : 0 < q) (h : IsNormalDiag (I := I) Y hcomplete hconn x q δ e)
    (hf : NormalDiagFence (I := I) Y x q e) :
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
    letI : RiemannianBundle (fun y : Y.M ↦ TangentSpace I y) :=
      Y.riemBundle (I := I)
    letI : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
      Y.riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
      (fun y : Y.M ↦ TangentSpace I y) := Y.riemBundle_cont (I := I)
    letI : EMetricSpace Y.M := Y.emetricSpace (I := I)
    letI : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
    normalTanHome (I := I) Y x '' Metric.ball (0 : E × E) q =
        (toBranch (I := I) Y hcomplete hconn x hq h).hom.source ∧
      normalPairHome (I := I) Y x '' e.target =
        (toBranch (I := I) Y hcomplete hconn x hq h).dom ∧
      ∀ w ∈ e.target,
        (toBranch (I := I) Y hcomplete hconn x hq h).inv
            (normalPair (I := I) Y x w) =
          normalTangent (I := I) Y x (e.symm w) := by
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
  letI : RiemannianBundle (fun y : Y.M ↦ TangentSpace I y) :=
    Y.riemBundle (I := I)
  letI : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
    Y.riemInner (I := I)
  letI : IsContinuousRiemannianBundle E
      (fun y : Y.M ↦ TangentSpace I y) := Y.riemBundle_cont (I := I)
  letI : EMetricSpace Y.M := Y.emetricSpace (I := I)
  letI : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
  let A := normalTanHome (I := I) Y x
  let P := normalPairHome (I := I) Y x
  have hdata := h
  change e.source = Metric.ball (0 : E × E) q ∧
    e 0 = 0 ∧
    ContDiffOn Real ∞ (e : E × E → E × E) e.source ∧
    Metric.closedBall (0 : E × E) δ ⊆ e.target ∧
    ContDiffOn Real ∞ e.symm e.target ∧
    ∀ z ∈ Metric.closedBall (0 : E × E) q,
      normalPair (I := I) Y x (e z) =
        diagExp (I := I) Y.metric (normal_enorm (I := I) Y)
          (normalTangent (I := I) Y x z) at hdata
  rcases hdata with ⟨hsource, _hzero, _heInf, _htarget, _hinvInf, _hdiag⟩
  have hfence := hf
  change ∀ z ∈ Metric.closedBall (0 : E × E) q,
    z.1 ∈ normalBall (I := I) Y x ∧
    (e z).1 ∈ normalBall (I := I) Y x ∧
    (e z).2 ∈ normalBall (I := I) Y x at hfence
  have targetData : ∀ {w : E × E}, w ∈ e.target →
      w ∈ P.source ∧ e.symm w ∈ A.source := by
    intro w hw
    have hzSource : e.symm w ∈ e.source := e.map_target hw
    have hzBall : e.symm w ∈ Metric.ball (0 : E × E) q := by
      rw [← hsource]
      exact hzSource
    have hzFence := hfence (e.symm w) (Metric.ball_subset_closedBall hzBall)
    have hzA : e.symm w ∈ A.source := by
      change e.symm w ∈ (normalTanHome (I := I) Y x).source
      rw [normalTanHome_source]
      exact hzFence.1
    have hezP : e (e.symm w) ∈ P.source := by
      change e (e.symm w) ∈ (normalPairHome (I := I) Y x).source
      rw [normalPair_source]
      exact ⟨hzFence.2.1, hzFence.2.2⟩
    have hwP : w ∈ P.source := by
      rw [e.right_inv hw] at hezP
      exact hezP
    exact ⟨hwP, hzA⟩
  have hsourceTransport : A '' Metric.ball (0 : E × E) q =
      (toBranch (I := I) Y hcomplete hconn x hq h).hom.source := by
    rw [toBranch_hom]
    ext u
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hzFence := hfence z (Metric.ball_subset_closedBall hz)
      have hzA : z ∈ A.source := by
        change z ∈ (normalTanHome (I := I) Y x).source
        rw [normalTanHome_source]
        exact hzFence.1
      have hezP : e z ∈ P.source := by
        change e z ∈ (normalPairHome (I := I) Y x).source
        rw [normalPair_source]
        exact ⟨hzFence.2.1, hzFence.2.2⟩
      change A z ∈ (A.symm.trans (e.trans P)).source
      rw [OpenPartialHomeomorph.trans_source]
      refine ⟨A.map_source hzA, ?_⟩
      change A.symm (A z) ∈ (e.trans P).source
      rw [A.left_inv hzA, OpenPartialHomeomorph.trans_source]
      exact ⟨by rwa [hsource], hezP⟩
    · intro hu
      change u ∈ (A.symm.trans (e.trans P)).source at hu
      rw [OpenPartialHomeomorph.trans_source] at hu
      rcases hu with ⟨huA, huRest⟩
      change A.symm u ∈ (e.trans P).source at huRest
      rw [OpenPartialHomeomorph.trans_source] at huRest
      refine ⟨A.symm u, ?_, A.right_inv huA⟩
      rw [← hsource]
      exact huRest.1
  have htargetTransport : P '' e.target =
      (toBranch (I := I) Y hcomplete hconn x hq h).dom := by
    unfold DiagInvBranch.dom
    rw [toBranch_hom]
    ext y
    constructor
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨hwP, hzA⟩ := targetData hw
      change P w ∈ (A.symm.trans (e.trans P)).target
      rw [OpenPartialHomeomorph.trans_target]
      constructor
      · change P w ∈ (e.trans P).target
        rw [OpenPartialHomeomorph.trans_target]
        refine ⟨P.map_source hwP, ?_⟩
        change P.symm (P w) ∈ e.target
        rwa [P.left_inv hwP]
      · change (e.trans P).symm (P w) ∈ A.source
        change e.symm (P.symm (P w)) ∈ A.source
        rwa [P.left_inv hwP]
    · intro hy
      change y ∈ (A.symm.trans (e.trans P)).target at hy
      rw [OpenPartialHomeomorph.trans_target] at hy
      have hyRest := hy.1
      change y ∈ (e.trans P).target at hyRest
      rw [OpenPartialHomeomorph.trans_target] at hyRest
      exact ⟨P.symm y, hyRest.2, P.right_inv hyRest.1⟩
  refine ⟨hsourceTransport, htargetTransport, ?_⟩
  intro w hw
  obtain ⟨hwP, hzA⟩ := targetData hw
  have hzNormal : (e.symm w).1 ∈ normalBall (I := I) Y x := by
    change e.symm w ∈ (normalTanHome (I := I) Y x).source at hzA
    rw [normalTanHome_source] at hzA
    exact hzA
  unfold DiagInvBranch.inv
  rw [toBranch_hom]
  change (normalDiagHome (I := I) Y x e).symm
      (normalPair (I := I) Y x w) =
    normalTangent (I := I) Y x (e.symm w)
  rw [← normalPairHome_apply (I := I) Y x w]
  change A (e.symm (P.symm (P w))) =
    normalTangent (I := I) Y x (e.symm w)
  rw [P.left_inv hwP]
  exact normalTanHome_apply (I := I) Y x (e.symm w) hzNormal



theorem symm_fst_eq
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (hcomplete : MetricComplete (I := I) Y)
    (hconn : letI : TopologicalSpace Y.M := Y.topology; ConnectedSpace Y.M)
    (x : Y.M) {q : NNReal} {δ : Real}
    {e : OpenPartialHomeomorph (E × E) (E × E)}
    (h : IsNormalDiag (I := I) Y hcomplete hconn x q δ e)
    (hf : NormalDiagFence (I := I) Y x q e) {w : E × E}
    (hw : w ∈ e.target) :
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
    letI : RiemannianBundle (fun y : Y.M ↦ TangentSpace I y) :=
      Y.riemBundle (I := I)
    letI : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
      Y.riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
      (fun y : Y.M ↦ TangentSpace I y) := Y.riemBundle_cont (I := I)
    letI : EMetricSpace Y.M := Y.emetricSpace (I := I)
    letI : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
    (e.symm w).1 = w.1 := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : IsManifold I 1 Y.M := IsManifold.of_le
    (I := I) (M := Y.M) (n := ∞) (by decide)
  letI : SigmaCompactSpace Y.M := Y.sigmaCompact
  letI : T2Space Y.M := Y.t2
  letI : ConnectedSpace Y.M := hconn
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  letI : TopologicalSpace.MetrizableSpace Y.M := Manifold.metrizableSpace I Y.M
  letI : T3Space Y.M := inferInstance
  letI : RiemannianBundle (fun y : Y.M ↦ TangentSpace I y) :=
    Y.riemBundle (I := I)
  letI : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
    Y.riemInner (I := I)
  letI : IsContinuousRiemannianBundle E
      (fun y : Y.M ↦ TangentSpace I y) := Y.riemBundle_cont (I := I)
  letI : EMetricSpace Y.M := Y.emetricSpace (I := I)
  letI : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
  have hdata := h
  change e.source = Metric.ball (0 : E × E) q ∧
    e 0 = 0 ∧
    ContDiffOn Real ∞ (e : E × E → E × E) e.source ∧
    Metric.closedBall (0 : E × E) δ ⊆ e.target ∧
    ContDiffOn Real ∞ e.symm e.target ∧
    ∀ z ∈ Metric.closedBall (0 : E × E) q,
      normalPair (I := I) Y x (e z) =
        diagExp (I := I) Y.metric (normal_enorm (I := I) Y)
          (normalTangent (I := I) Y x z) at hdata
  rcases hdata with ⟨hsource, _hzero, _heInf, _htarget, _hinvInf, hdiag⟩
  have hfence := hf
  change ∀ z ∈ Metric.closedBall (0 : E × E) q,
    z.1 ∈ normalBall (I := I) Y x ∧
    (e z).1 ∈ normalBall (I := I) Y x ∧
    (e z).2 ∈ normalBall (I := I) Y x at hfence
  have hzSource : e.symm w ∈ e.source := e.map_target hw
  have hzBall : e.symm w ∈ Metric.ball (0 : E × E) q := by
    rw [← hsource]
    exact hzSource
  have hzFence := hfence (e.symm w) (Metric.ball_subset_closedBall hzBall)
  have hzNormal : (e.symm w).1 ∈ normalBall (I := I) Y x := hzFence.1
  have hwNormal : w.1 ∈ normalBall (I := I) Y x := by
    rw [← e.right_inv hw]
    exact hzFence.2.1
  have hfst := congrArg Prod.fst
    (hdiag (e.symm w) (Metric.ball_subset_closedBall hzBall))
  have hexp :
      NormalCoordinates.expMapDiffeo (I := I) Y.metric x w.1 =
        NormalCoordinates.expMapDiffeo (I := I) Y.metric x (e.symm w).1 := by
    simpa only [normalPair, normalTangent, diagExp_fst, e.right_inv hw] using hfst
  apply (normalExpPD (I := I) Y x).toPartialEquiv.injOn
  · simpa only [normalExpPD_source] using hzNormal
  · simpa only [normalExpPD_source] using hwNormal
  · exact hexp.symm



theorem inv_pair_normal
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (hcomplete : MetricComplete (I := I) Y)
    (hconn : letI : TopologicalSpace Y.M := Y.topology; ConnectedSpace Y.M)
    (x : Y.M) {q : NNReal} {δ : Real}
    {e : OpenPartialHomeomorph (E × E) (E × E)}
    (hq : 0 < q) (h : IsNormalDiag (I := I) Y hcomplete hconn x q δ e)
    (hf : NormalDiagFence (I := I) Y x q e) {w : E × E}
    (hw : w ∈ e.target) :
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
    letI : RiemannianBundle (fun y : Y.M ↦ TangentSpace I y) :=
      Y.riemBundle (I := I)
    letI : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
      Y.riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
      (fun y : Y.M ↦ TangentSpace I y) := Y.riemBundle_cont (I := I)
    letI : EMetricSpace Y.M := Y.emetricSpace (I := I)
    letI : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
    (toBranch (I := I) Y hcomplete hconn x hq h).inv
        (normalPair (I := I) Y x w) =
      normalTangent (I := I) Y x (w.1, (e.symm w).2) := by
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
  letI : RiemannianBundle (fun y : Y.M ↦ TangentSpace I y) :=
    Y.riemBundle (I := I)
  letI : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
    Y.riemInner (I := I)
  letI : IsContinuousRiemannianBundle E
    (fun y : Y.M ↦ TangentSpace I y) := Y.riemBundle_cont (I := I)
  letI : EMetricSpace Y.M := Y.emetricSpace (I := I)
  letI : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
  rw [(full_transport (I := I) Y hcomplete hconn x hq h hf).2.2 w hw]
  congr 1
  exact Prod.ext (symm_fst_eq (I := I) Y hcomplete hconn x h hf hw) rfl



theorem target_of_pair_mem
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (hcomplete : MetricComplete (I := I) Y)
    (hconn : letI : TopologicalSpace Y.M := Y.topology; ConnectedSpace Y.M)
    (x : Y.M) {q : NNReal} {δ : Real}
    {e : OpenPartialHomeomorph (E × E) (E × E)}
    (hq : 0 < q) (h : IsNormalDiag (I := I) Y hcomplete hconn x q δ e) :
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
    letI : RiemannianBundle (fun y : Y.M ↦ TangentSpace I y) :=
      Y.riemBundle (I := I)
    letI : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
      Y.riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
      (fun y : Y.M ↦ TangentSpace I y) := Y.riemBundle_cont (I := I)
    letI : EMetricSpace Y.M := Y.emetricSpace (I := I)
    letI : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
    ∀ {w : E × E}, w ∈ (normalPairHome (I := I) Y x).source →
      normalPair (I := I) Y x w ∈
        (toBranch (I := I) Y hcomplete hconn x hq h).dom →
      w ∈ e.target := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : IsManifold I 1 Y.M := IsManifold.of_le
    (I := I) (M := Y.M) (n := ∞) (by decide)
  letI : SigmaCompactSpace Y.M := Y.sigmaCompact
  letI : T2Space Y.M := Y.t2
  letI : ConnectedSpace Y.M := hconn
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  letI : TopologicalSpace.MetrizableSpace Y.M := Manifold.metrizableSpace I Y.M
  letI : T3Space Y.M := inferInstance
  letI : RiemannianBundle (fun y : Y.M ↦ TangentSpace I y) :=
    Y.riemBundle (I := I)
  letI : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
    Y.riemInner (I := I)
  letI : IsContinuousRiemannianBundle E
      (fun y : Y.M ↦ TangentSpace I y) := Y.riemBundle_cont (I := I)
  letI : EMetricSpace Y.M := Y.emetricSpace (I := I)
  letI : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
  intro w hw hdom
  let A := normalTanHome (I := I) Y x
  let P := normalPairHome (I := I) Y x
  unfold DiagInvBranch.dom at hdom
  rw [toBranch_hom (I := I) Y hcomplete hconn x hq h] at hdom
  change P w ∈ (A.symm.trans (e.trans P)).target at hdom
  rw [OpenPartialHomeomorph.trans_target] at hdom
  have hrest := hdom.1
  rw [OpenPartialHomeomorph.trans_target] at hrest
  have htarget : P.symm (P w) ∈ e.target := hrest.2
  rwa [P.left_inv hw] at htarget



theorem target_of_chart_dom
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (hcomplete : MetricComplete (I := I) Y)
    (hconn : letI : TopologicalSpace Y.M := Y.topology; ConnectedSpace Y.M)
    (x : Y.M) {q : NNReal} {δ : Real}
    {e : OpenPartialHomeomorph (E × E) (E × E)}
    (hq : 0 < q) (h : IsNormalDiag (I := I) Y hcomplete hconn x q δ e)
    (hf : NormalDiagFence (I := I) Y x q e) {y p : Y.M} :
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
    y ∈ (NormalCoordinates.normalChartAt (I := I) Y.metric x).source →
      p ∈ (NormalCoordinates.normalChartAt (I := I) Y.metric x).source →
      (y, p) ∈ (toBranch (I := I) Y hcomplete hconn x hq h).dom →
      (NormalCoordinates.normalChartAt (I := I) Y.metric x y,
        NormalCoordinates.normalChartAt (I := I) Y.metric x p) ∈ e.target := by
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
  intro hy hp hdom
  let P := normalPairHome (I := I) Y x
  have htransport := full_transport (I := I) Y hcomplete hconn x hq h hf
  have himage : (y, p) ∈ P '' e.target := by
    rw [htransport.2.1]
    exact hdom
  obtain ⟨w, hw, hwEq⟩ := himage
  have hdata := h
  change e.source = Metric.ball (0 : E × E) q ∧
    e 0 = 0 ∧
    ContDiffOn Real ∞ (e : E × E → E × E) e.source ∧
    Metric.closedBall (0 : E × E) δ ⊆ e.target ∧
    ContDiffOn Real ∞ e.symm e.target ∧
    ∀ z ∈ Metric.closedBall (0 : E × E) q,
      normalPair (I := I) Y x (e z) =
        diagExp (I := I) Y.metric (normal_enorm (I := I) Y)
          (normalTangent (I := I) Y x z) at hdata
  have hwBall : e.symm w ∈ Metric.ball (0 : E × E) q := by
    rw [← hdata.1]
    exact e.map_target hw
  have hfence := hf
  change ∀ z ∈ Metric.closedBall (0 : E × E) q,
    z.1 ∈ normalBall (I := I) Y x ∧
    (e z).1 ∈ normalBall (I := I) Y x ∧
    (e z).2 ∈ normalBall (I := I) Y x at hfence
  have hwNormal : w.1 ∈ normalBall (I := I) Y x ∧
      w.2 ∈ normalBall (I := I) Y x := by
    have hout := (hfence (e.symm w)
      (Metric.ball_subset_closedBall hwBall)).2
    simpa only [e.right_inv hw] using hout
  have hwP : w ∈ P.source := by
    change w ∈ (normalPairHome (I := I) Y x).source
    rw [normalPair_source]
    exact hwNormal
  have hleft := P.left_inv hwP
  change
    (NormalCoordinates.normalChartAt (I := I) Y.metric x (P w).1,
      NormalCoordinates.normalChartAt (I := I) Y.metric x (P w).2) = w at hleft
  rw [hwEq] at hleft
  have hcoordSource :
      (NormalCoordinates.normalChartAt (I := I) Y.metric x y,
        NormalCoordinates.normalChartAt (I := I) Y.metric x p) ∈ P.source := by
    rw [hleft]
    exact hwP
  have hpairEq :
      normalPair (I := I) Y x
        (NormalCoordinates.normalChartAt (I := I) Y.metric x y,
          NormalCoordinates.normalChartAt (I := I) Y.metric x p) = (y, p) := by
    change
      ((NormalCoordinates.normalChartAt (I := I) Y.metric x).symm
          (NormalCoordinates.normalChartAt (I := I) Y.metric x y),
        (NormalCoordinates.normalChartAt (I := I) Y.metric x).symm
          (NormalCoordinates.normalChartAt (I := I) Y.metric x p)) = (y, p)
    rw [NormalCoordinates.normalChartAt_left_inv (I := I) Y.metric x hy,
      NormalCoordinates.normalChartAt_left_inv (I := I) Y.metric x hp]
  apply target_of_pair_mem (I := I) Y hcomplete hconn x hq h hcoordSource
  rwa [hpairEq]




theorem pair_mem_of_closed
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (hcomplete : MetricComplete (I := I) Y)
    (hconn : letI : TopologicalSpace Y.M := Y.topology; ConnectedSpace Y.M)
    (x : Y.M) {q : NNReal} {δ ρ : Real}
    {e : OpenPartialHomeomorph (E × E) (E × E)}
    (hq : 0 < q) (h : IsNormalDiag (I := I) Y hcomplete hconn x q δ e)
    {w : E × E} (hw : w ∈ Metric.closedBall (0 : E × E) ρ) :
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
    letI : RiemannianBundle (fun y : Y.M => TangentSpace I y) :=
      Y.riemBundle (I := I)
    letI : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
      Y.riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
      (fun y : Y.M => TangentSpace I y) := Y.riemBundle_cont (I := I)
    letI : EMetricSpace Y.M := Y.emetricSpace (I := I)
    letI : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
    (q : Real) < expMapC2Radius (I := I) Y.metric x →
    ρ ≤ δ →
    ρ < expMapC2Radius (I := I) Y.metric x →
      normalPair (I := I) Y x w ∈
        (toBranch (I := I) Y hcomplete hconn x hq h).dom := by
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
  letI : RiemannianBundle (fun y : Y.M => TangentSpace I y) :=
    Y.riemBundle (I := I)
  letI : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
    Y.riemInner (I := I)
  letI : IsContinuousRiemannianBundle E
      (fun y : Y.M => TangentSpace I y) := Y.riemBundle_cont (I := I)
  letI : EMetricSpace Y.M := Y.emetricSpace (I := I)
  letI : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
  intro hqExp hρδ hρExp
  change e.source = Metric.ball (0 : E × E) q ∧
    e 0 = 0 ∧
    ContDiffOn Real ∞ (e : E × E → E × E) e.source ∧
    Metric.closedBall (0 : E × E) δ ⊆ e.target ∧
    ContDiffOn Real ∞ e.symm e.target ∧
    ∀ z ∈ Metric.closedBall (0 : E × E) q,
      normalPair (I := I) Y x (e z) =
        diagExp (I := I) Y.metric (normal_enorm (I := I) Y)
          (normalTangent (I := I) Y x z) at h
  rcases h with ⟨hsource, _hzero, _heInf, htarget, _hinvInf, _hdiag⟩
  let A := normalTanHome (I := I) Y x
  let P := normalPairHome (I := I) Y x
  have hwnorm : ‖w‖ ≤ ρ := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hw
  have hwP : w ∈ P.source := by
    change w ∈ (normalPairHome (I := I) Y x).source
    rw [normalPair_source]
    constructor
    · change dist w.1 0 < expMapC2Radius (I := I) Y.metric x
      rw [dist_zero_right]
      exact (norm_fst_le w).trans_lt (hwnorm.trans_lt hρExp)
    · change dist w.2 0 < expMapC2Radius (I := I) Y.metric x
      rw [dist_zero_right]
      exact (norm_snd_le w).trans_lt (hwnorm.trans_lt hρExp)
  have hwe : w ∈ e.target :=
    htarget (Metric.closedBall_subset_closedBall hρδ hw)
  have hwinv : e.symm w ∈ e.source := e.map_target hwe
  have hwinvBall : e.symm w ∈ Metric.ball (0 : E × E) q := by
    rw [← hsource]
    exact hwinv
  have hwinvNorm : ‖e.symm w‖ < (q : Real) := by
    simpa only [Metric.mem_ball, dist_zero_right] using hwinvBall
  have hwA : e.symm w ∈ A.source := by
    change e.symm w ∈ (normalTanHome (I := I) Y x).source
    rw [normalTanHome_source]
    change dist (e.symm w).1 0 < expMapC2Radius (I := I) Y.metric x
    rw [dist_zero_right]
    exact (norm_fst_le (e.symm w)).trans_lt (hwinvNorm.trans hqExp)
  unfold DiagInvBranch.dom
  change normalPair (I := I) Y x w ∈ (normalDiagHome (I := I) Y x e).target
  rw [← normalPairHome_apply (I := I) Y x w]
  exact pair_mem_target A e P hwP hwe hwA

end IsNormalDiag



def HasNormalBranchDom
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (hcomplete : MetricComplete (I := I) Y)
    (hconn : letI : TopologicalSpace Y.M := Y.topology; ConnectedSpace Y.M)
    (x : Y.M) (q : NNReal) (δ ρ : Real) : Prop := by
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
  letI : RiemannianBundle (fun y : Y.M => TangentSpace I y) :=
    Y.riemBundle (I := I)
  letI : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
    Y.riemInner (I := I)
  letI : IsContinuousRiemannianBundle E
      (fun y : Y.M => TangentSpace I y) := Y.riemBundle_cont (I := I)
  letI : EMetricSpace Y.M := Y.emetricSpace (I := I)
  letI : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
  exact ∃ hq : 0 < q,
    ∃ e : OpenPartialHomeomorph (E × E) (E × E),
      ∃ he : IsNormalDiag (I := I) Y hcomplete hconn x q δ e,
        ∀ w ∈ Metric.closedBall (0 : E × E) ρ,
          normalPair (I := I) Y x w ∈
            (IsNormalDiag.toBranch (I := I) Y hcomplete hconn x hq he).dom

namespace HasNormalBranchDom



theorem exists_pair_branch
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hb : NormalCoordMetricBoundInput (I := I) X) (k : Nat)
    (hcomplete : MetricComplete (I := I) (X.obj k))
    (hconn : letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (x : (X.obj k).M) {q : NNReal} {δ ρ : Real}
    (hdom : HasNormalBranchDom (I := I) (X.obj k) hcomplete hconn x q δ ρ)
    {ι : Type*} (a b : ι → (X.obj k).M) :
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
    letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    letI : IsManifold I 1 (X.obj k).M := IsManifold.of_le
      (I := I) (M := (X.obj k).M) (n := ∞) (by decide)
    letI : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
    letI : T2Space (X.obj k).M := (X.obj k).t2
    letI : ConnectedSpace (X.obj k).M := hconn
    letI : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    letI : TopologicalSpace.MetrizableSpace (X.obj k).M :=
      Manifold.metrizableSpace I (X.obj k).M
    letI : T3Space (X.obj k).M := inferInstance
    letI : RiemannianBundle
        (fun y : (X.obj k).M ↦ TangentSpace I y) :=
      (X.obj k).riemBundle (I := I)
    letI : (y : (X.obj k).M) → InnerProductSpace Real (TangentSpace I y) :=
      (X.obj k).riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
        (fun y : (X.obj k).M ↦ TangentSpace I y) :=
      (X.obj k).riemBundle_cont (I := I)
    letI : EMetricSpace (X.obj k).M := (X.obj k).emetricSpace (I := I)
    letI : CompleteSpace (X.obj k).M :=
      MetricComplete.complete (I := I) (X.obj k) hcomplete
    0 < ρ →
      ρ / 2 < expRadiusGp (I := I) (X.obj k).metric x →
      (∀ i, max (riemannianEDist I x (a i)) (riemannianEDist I x (b i)) <
        ENNReal.ofReal (ρ / 2)) →
      ∃ B : DiagInvBranch (I := I) (X.obj k).metric
          (normal_enorm (I := I) (X.obj k)) x,
        ∀ i, (a i, b i) ∈ B.dom := by
  letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
  letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
  letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  letI : IsManifold I 1 (X.obj k).M := IsManifold.of_le
    (I := I) (M := (X.obj k).M) (n := ∞) (by decide)
  letI : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
  letI : T2Space (X.obj k).M := (X.obj k).t2
  letI : ConnectedSpace (X.obj k).M := hconn
  letI : T2Space (TangentBundle I (X.obj k).M) :=
    (X.obj k).t2TangentBundle
  letI : TopologicalSpace.MetrizableSpace (X.obj k).M :=
    Manifold.metrizableSpace I (X.obj k).M
  letI : T3Space (X.obj k).M := inferInstance
  letI : RiemannianBundle (fun y : (X.obj k).M ↦ TangentSpace I y) :=
    (X.obj k).riemBundle (I := I)
  letI : (y : (X.obj k).M) → InnerProductSpace Real (TangentSpace I y) :=
    (X.obj k).riemInner (I := I)
  letI : IsContinuousRiemannianBundle E
      (fun y : (X.obj k).M ↦ TangentSpace I y) :=
    (X.obj k).riemBundle_cont (I := I)
  letI : EMetricSpace (X.obj k).M := (X.obj k).emetricSpace (I := I)
  letI : CompleteSpace (X.obj k).M :=
    MetricComplete.complete (I := I) (X.obj k) hcomplete
  intro hρ hρExp hpairs
  change ∃ hq : 0 < q,
    ∃ e : OpenPartialHomeomorph (E × E) (E × E),
      ∃ he : IsNormalDiag (I := I) (X.obj k) hcomplete hconn x q δ e,
        ∀ w ∈ Metric.closedBall (0 : E × E) ρ,
          normalPair (I := I) (X.obj k) x w ∈
            (IsNormalDiag.toBranch (I := I) (X.obj k) hcomplete hconn x hq he).dom at hdom
  obtain ⟨hq, e, he, hclosed⟩ := hdom
  refine ⟨IsNormalDiag.toBranch (I := I) (X.obj k) hcomplete hconn x hq he, ?_⟩
  intro i
  have haLt : riemannianEDist I x (a i) < ENNReal.ofReal (ρ / 2) :=
    (le_max_left _ _).trans_lt (hpairs i)
  have hbLt : riemannianEDist I x (b i) < ENNReal.ofReal (ρ / 2) :=
    (le_max_right _ _).trans_lt (hpairs i)
  have haFin : riemannianEDist I x (a i) ≠ ⊤ :=
    ne_of_lt (haLt.trans ENNReal.ofReal_lt_top)
  have hbFin : riemannianEDist I x (b i) ≠ ⊤ :=
    ne_of_lt (hbLt.trans ENNReal.ofReal_lt_top)
  have haReal : (riemannianEDist I x (a i)).toReal < ρ / 2 :=
    (ENNReal.lt_ofReal_iff_toReal_lt haFin).mp haLt
  have hbReal : (riemannianEDist I x (b i)).toReal < ρ / 2 :=
    (ENNReal.lt_ofReal_iff_toReal_lt hbFin).mp hbLt
  have haControl := hb.chart_mem_norm_le k x (a i) ⟨haFin, haReal.trans hρExp⟩
  have hbControl := hb.chart_mem_norm_le k x (b i) ⟨hbFin, hbReal.trans hρExp⟩
  let wa := NormalCoordinates.normalChartAt (I := I) (X.obj k).metric x (a i)
  let wb := NormalCoordinates.normalChartAt (I := I) (X.obj k).metric x (b i)
  have hwa : ‖wa‖ < ρ := by
    calc
      ‖wa‖ ≤ 2 * (riemannianEDist I x (a i)).toReal := haControl.2
      _ < 2 * (ρ / 2) := mul_lt_mul_of_pos_left haReal (by norm_num)
      _ = ρ := by ring
  have hwb : ‖wb‖ < ρ := by
    calc
      ‖wb‖ ≤ 2 * (riemannianEDist I x (b i)).toReal := hbControl.2
      _ < 2 * (ρ / 2) := mul_lt_mul_of_pos_left hbReal (by norm_num)
      _ = ρ := by ring
  have hwClosed : (wa, wb) ∈ Metric.closedBall (0 : E × E) ρ := by
    rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]
    exact max_le hwa.le hwb.le
  have haTarget : wa ∈
      (NormalCoordinates.normalChartAt (I := I) (X.obj k).metric x).target :=
    (NormalCoordinates.normalChartAt (I := I) (X.obj k).metric x).map_source haControl.1
  have hbTarget : wb ∈
      (NormalCoordinates.normalChartAt (I := I) (X.obj k).metric x).target :=
    (NormalCoordinates.normalChartAt (I := I) (X.obj k).metric x).map_source hbControl.1
  have haDecode : NormalCoordinates.expMapDiffeo (I := I) (X.obj k).metric x wa = a i := by
    calc
      NormalCoordinates.expMapDiffeo (I := I) (X.obj k).metric x wa =
          expMap (I := I) (X.obj k).metric x wa :=
        NormalCoordinates.expMapDiffeo_apply_eq
          (I := I) (X.obj k).metric x haTarget
      _ =
          (NormalCoordinates.normalChartAt (I := I) (X.obj k).metric x).symm wa :=
        (NormalCoordinates.normalChartAt_symm_apply
          (I := I) (X.obj k).metric x haTarget).symm
      _ = a i :=
        (NormalCoordinates.normalChartAt (I := I) (X.obj k).metric x).left_inv haControl.1
  have hbDecode : NormalCoordinates.expMapDiffeo (I := I) (X.obj k).metric x wb = b i := by
    calc
      NormalCoordinates.expMapDiffeo (I := I) (X.obj k).metric x wb =
          expMap (I := I) (X.obj k).metric x wb :=
        NormalCoordinates.expMapDiffeo_apply_eq
          (I := I) (X.obj k).metric x hbTarget
      _ =
          (NormalCoordinates.normalChartAt (I := I) (X.obj k).metric x).symm wb :=
        (NormalCoordinates.normalChartAt_symm_apply
          (I := I) (X.obj k).metric x hbTarget).symm
      _ = b i :=
        (NormalCoordinates.normalChartAt (I := I) (X.obj k).metric x).left_inv hbControl.1
  have hnormalPair : normalPair (I := I) (X.obj k) x (wa, wb) = (a i, b i) := by
    change (NormalCoordinates.expMapDiffeo (I := I) (X.obj k).metric x wa,
      NormalCoordinates.expMapDiffeo (I := I) (X.obj k).metric x wb) = (a i, b i)
    rw [haDecode, hbDecode]
  rw [← hnormalPair]
  exact hclosed (wa, wb) hwClosed



theorem exists_pair_readout
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hb : NormalCoordMetricBoundInput (I := I) X) (k : Nat)
    (hcomplete : MetricComplete (I := I) (X.obj k))
    (hconn : letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (x : (X.obj k).M) {q : NNReal} {δ ρ : Real}
    (hdom : HasNormalBranchDom (I := I) (X.obj k) hcomplete hconn x q δ ρ)
    {ι : Type*} (a b : ι → (X.obj k).M) :
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
    letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    letI : IsManifold I 1 (X.obj k).M := IsManifold.of_le
      (I := I) (M := (X.obj k).M) (n := ∞) (by decide)
    letI : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
    letI : T2Space (X.obj k).M := (X.obj k).t2
    letI : ConnectedSpace (X.obj k).M := hconn
    letI : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    letI : TopologicalSpace.MetrizableSpace (X.obj k).M :=
      Manifold.metrizableSpace I (X.obj k).M
    letI : T3Space (X.obj k).M := inferInstance
    letI : RiemannianBundle
        (fun y : (X.obj k).M ↦ TangentSpace I y) :=
      (X.obj k).riemBundle (I := I)
    letI : (y : (X.obj k).M) → InnerProductSpace Real (TangentSpace I y) :=
      (X.obj k).riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
        (fun y : (X.obj k).M ↦ TangentSpace I y) :=
      (X.obj k).riemBundle_cont (I := I)
    letI : EMetricSpace (X.obj k).M := (X.obj k).emetricSpace (I := I)
    letI : CompleteSpace (X.obj k).M :=
      MetricComplete.complete (I := I) (X.obj k) hcomplete
    0 < ρ →
      ρ / 2 < expRadiusGp (I := I) (X.obj k).metric x →
      (∀ i, max (riemannianEDist I x (a i)) (riemannianEDist I x (b i)) <
        ENNReal.ofReal (ρ / 2)) →
      ∃ B : DiagInvBranch (I := I) (X.obj k).metric
          (normal_enorm (I := I) (X.obj k)) x,
        ∀ i, (a i, b i) ∈ B.readDom := by
  letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
  letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
  letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  letI : IsManifold I 1 (X.obj k).M := IsManifold.of_le
    (I := I) (M := (X.obj k).M) (n := ∞) (by decide)
  letI : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
  letI : T2Space (X.obj k).M := (X.obj k).t2
  letI : ConnectedSpace (X.obj k).M := hconn
  letI : T2Space (TangentBundle I (X.obj k).M) :=
    (X.obj k).t2TangentBundle
  letI : TopologicalSpace.MetrizableSpace (X.obj k).M :=
    Manifold.metrizableSpace I (X.obj k).M
  letI : T3Space (X.obj k).M := inferInstance
  letI : RiemannianBundle (fun y : (X.obj k).M ↦ TangentSpace I y) :=
    (X.obj k).riemBundle (I := I)
  letI : (y : (X.obj k).M) → InnerProductSpace Real (TangentSpace I y) :=
    (X.obj k).riemInner (I := I)
  letI : IsContinuousRiemannianBundle E
      (fun y : (X.obj k).M ↦ TangentSpace I y) :=
    (X.obj k).riemBundle_cont (I := I)
  letI : EMetricSpace (X.obj k).M := (X.obj k).emetricSpace (I := I)
  letI : CompleteSpace (X.obj k).M :=
    MetricComplete.complete (I := I) (X.obj k) hcomplete
  intro hρ hρExp hpairs
  obtain ⟨B, hB⟩ := exists_pair_branch (I := I) hb k hcomplete hconn x hdom
    a b hρ hρExp hpairs
  refine ⟨B, fun i => ⟨hB i, ?_⟩⟩
  have haLt : riemannianEDist I x (a i) < ENNReal.ofReal (ρ / 2) :=
    (le_max_left _ _).trans_lt (hpairs i)
  have haFin : riemannianEDist I x (a i) ≠ ⊤ :=
    ne_of_lt (haLt.trans ENNReal.ofReal_lt_top)
  have haReal : (riemannianEDist I x (a i)).toReal < ρ / 2 :=
    (ENNReal.lt_ofReal_iff_toReal_lt haFin).mp haLt
  have haSource :=
    (hb.chart_mem_norm_le k x (a i) ⟨haFin, haReal.trans hρExp⟩).1
  rw [TangentBundle.trivializationAt_baseSet]
  apply NormalCoordinates.exp_target_sub_chart (I := I) (X.obj k).metric x
  rwa [← NormalCoordinates.normalChartAt_source_eq]

end HasNormalBranchDom

namespace NormalRadiusProfile



theorem exists_common_dom
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    {hb : NormalCoordMetricBoundInput (I := I) X}
    (h : NormalRadiusProfile hd hb)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (R : Real) :
    ∃ (q : NNReal) (δ ρ : Real),
      0 < q ∧ 0 < δ ∧ 0 < ρ ∧ ρ ≤ δ ∧
      4 * (q : Real) < h.phaseRadius R ∧
      δ = ((‖((PhaseFlow.freeDiagCLE (E := E)).symm :
        (E × E) →L[Real] (E × E))‖₊⁻¹ -
          PhaseFlow.phaseErr (normalPhaseK hb (2 * q)) : NNReal) : Real) *
        ((q : Real) / 2) ∧
      ∀ k (x : (X.obj k).M),
        hd.dist k x (X.obj k).basepoint ≤ R →
        HasNormalBranchDom (I := I) (X.obj k) (hcomplete.complete k)
          (hconn k) x q δ ρ := by
  obtain ⟨q, δ, hq, hqRadius, hδ, hδeq, hall⟩ :=
    h.exists_uniform_diag hcomplete hconn R
  let ρ : Real := min δ ((q : Real) / 2)
  have hqReal : (0 : Real) < q := by exact_mod_cast hq
  have hρ : 0 < ρ := by
    dsimp only [ρ]
    exact lt_min hδ (div_pos hqReal (by norm_num))
  have hρδ : ρ ≤ δ := by
    exact min_le_left _ _
  have hρq : ρ < (q : Real) := by
    have hhalf : (q : Real) / 2 < q := by linarith
    exact (min_le_right _ _).trans_lt hhalf
  have hqFloor : (q : Real) < h.ratio * hd.mu R := by
    have hqRadius' := hqRadius
    rw [phaseRadius] at hqRadius'
    nlinarith [h.floor_pos R]
  refine ⟨q, δ, ρ, hq, hδ, hρ, hρδ, hqRadius, hδeq, ?_⟩
  intro k x hx
  letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
  letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
  letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  letI : IsManifold I 1 (X.obj k).M := IsManifold.of_le
    (I := I) (M := (X.obj k).M) (n := ∞) (by decide)
  letI : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
  letI : T2Space (X.obj k).M := (X.obj k).t2
  letI : ConnectedSpace (X.obj k).M := hconn k
  letI : T2Space (TangentBundle I (X.obj k).M) :=
    (X.obj k).t2TangentBundle
  letI : TopologicalSpace.MetrizableSpace (X.obj k).M :=
    Manifold.metrizableSpace I (X.obj k).M
  letI : T3Space (X.obj k).M := inferInstance
  letI : RiemannianBundle
      (fun y : (X.obj k).M => TangentSpace I y) :=
    (X.obj k).riemBundle (I := I)
  letI : (y : (X.obj k).M) → InnerProductSpace Real (TangentSpace I y) :=
    (X.obj k).riemInner (I := I)
  letI : IsContinuousRiemannianBundle E
      (fun y : (X.obj k).M => TangentSpace I y) :=
    (X.obj k).riemBundle_cont (I := I)
  letI : EMetricSpace (X.obj k).M := (X.obj k).emetricSpace (I := I)
  letI : CompleteSpace (X.obj k).M :=
    MetricComplete.complete (I := I) (X.obj k) (hcomplete.complete k)
  have hqExp : (q : Real) < expMapC2Radius (I := I) (X.obj k).metric x :=
    hqFloor.trans_le (h.floor_le_exp hx)
  have hρExp : ρ < expMapC2Radius (I := I) (X.obj k).metric x :=
    hρq.trans hqExp
  obtain ⟨e, he⟩ := hall k x hx
  change ∃ hq' : 0 < q,
    ∃ e : OpenPartialHomeomorph (E × E) (E × E),
      ∃ he : IsNormalDiag (I := I) (X.obj k) (hcomplete.complete k) (hconn k)
          x q δ e,
        ∀ w ∈ Metric.closedBall (0 : E × E) ρ,
          normalPair (I := I) (X.obj k) x w ∈
            (IsNormalDiag.toBranch (I := I) (X.obj k) (hcomplete.complete k)
              (hconn k) x hq' he).dom
  refine ⟨hq, e, he, ?_⟩
  intro w hw
  exact IsNormalDiag.pair_mem_of_closed (I := I) (X.obj k)
    (hcomplete.complete k) (hconn k) x hq he hw hqExp hρδ hρExp

end NormalRadiusProfile

end HCGCompactness
end DifferentialGeometry
