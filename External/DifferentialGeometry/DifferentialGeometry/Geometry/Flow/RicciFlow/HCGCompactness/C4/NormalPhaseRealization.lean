import DifferentialGeometry.Analysis.Calculus.RightDerivative
import DifferentialGeometry.Geometry.Connection.LeviCivita.CorrectionContraction
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.NormalPhase

set_option autoImplicit false









noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold ContDiff
open DifferentialGeometry.Geometry.Riemannian

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]



theorem normalPhaseVF_eq
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (x : Y.M) (a : E) (z : E × E) :
    Geodesic.chartPhaseVF (I := 𝓘(Real, E))
        (normalTotal (I := I) Y x) a z =
      PhaseFlow.phaseField (normalAccel (I := I) Y x) z := by
  unfold Geodesic.chartPhaseVF PhaseFlow.phaseField normalAccel
  rw [Integral.Connection.const_cov_eq_contr
    (g := normalTotal (I := I) Y x) (a := a)
    (z := z.1) (v := z.2) (w := z.2)]
  rfl



theorem normalPhase_contDiff
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    ContDiff Real ∞
      (PhaseFlow.phaseField (normalAccel (I := I) Y x) : E × E → E × E) := by
  have h := Geodesic.chartPhaseVF_contDiffOn (I := 𝓘(Real, E))
    (normalTotal (I := I) Y x) (0 : E)
  have heq := h.congr
    (fun z _ ↦ (normalPhaseVF_eq (I := I) Y x (0 : E) z).symm)
  have heq' : ContDiffOn Real ∞
      (PhaseFlow.phaseField (normalAccel (I := I) Y x) : E × E → E × E)
      Set.univ := by
    simpa only [extChartAt_model_space_eq_id, PartialEquiv.refl_target,
      interior_univ, Set.univ_prod_univ] using heq
  exact contDiffOn_univ.mp heq'



theorem normalGeoOn_of_phase
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (x : Y.M) {Z : Real → E × E} {s : Set Real} (hs : IsOpen s)
    (hZ : ∀ t ∈ s, HasDerivAt Z
      (PhaseFlow.phaseField (normalAccel (I := I) Y x) (Z t)) t) :
    Geodesic.IsGeodesicOn (I := 𝓘(Real, E))
      (normalTotal (I := I) Y x) (fun t ↦ (Z t).1) s := by
  intro t ht
  let gamma : Real → E := fun r ↦ (Z r).1
  let vel : Real → E := fun r ↦ (Z r).2
  have hgamma : ∀ r ∈ s, HasDerivAt gamma (vel r) r := by
    intro r hr
    have hfst := ((hZ r hr).hasFDerivAt.fst).hasDerivAt
    simpa only [gamma, vel, PhaseFlow.phaseField,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.toSpanSingleton_apply, one_smul] using hfst
  have hvel : ∀ r ∈ s, HasDerivAt vel
      (normalAccel (I := I) Y x (Z r)) r := by
    intro r hr
    have hsnd := ((hZ r hr).hasFDerivAt.snd).hasDerivAt
    simpa only [vel, PhaseFlow.phaseField, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_snd', ContinuousLinearMap.toSpanSingleton_apply,
      one_smul] using hsnd
  have hchart : Geodesic.chartLocalCurve (I := 𝓘(Real, E)) gamma t = gamma := by
    funext r
    simp only [Geodesic.chartLocalCurve_def, extChartAt_model_space_eq_id,
      PartialEquiv.refl_coe, id_eq]
  have hderiv : (fun r ↦ deriv gamma r) =ᶠ[nhds t] vel := by
    filter_upwards [hs.mem_nhds ht] with r hr
    exact (hgamma r hr).deriv
  have hacc : HasDerivAt (fun r ↦ deriv gamma r)
      (normalAccel (I := I) Y x (Z t)) t :=
    (hvel t ht).congr_of_eventuallyEq hderiv
  refine ⟨vel t, normalAccel (I := I) Y x (Z t), ?_, ?_, ?_, ?_⟩
  · simpa only [hchart] using hgamma t ht
  · filter_upwards [hs.mem_nhds ht] with r hr
    rw [hchart]
    simpa only [(hgamma r hr).deriv] using hgamma r hr
  · simpa only [hchart] using hacc
  · have hfield := congrArg Prod.snd
      (normalPhaseVF_eq (I := I) Y x (gamma t) (Z t))
    have hneg : -Geodesic.chartChristoffelContraction (I := 𝓘(Real, E))
        (normalTotal (I := I) Y x) (gamma t) (vel t) (vel t) (gamma t) =
          normalAccel (I := I) Y x (Z t) := by
      simpa only [Geodesic.chartPhaseVF, PhaseFlow.phaseField, gamma, vel] using hfield
    simp only [extChartAt_model_space_eq_id, PartialEquiv.refl_coe, id_eq]
    rw [← hneg]
    abel



theorem normalGeoOn_of_right
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (x : Y.M) {Z : Real → E × E} {a b : Real} (hab : a < b)
    (hZcont : ContinuousOn Z (Set.Icc a b))
    (hfield : ContinuousOn
      (fun t ↦ PhaseFlow.phaseField (normalAccel (I := I) Y x) (Z t))
      (Set.Icc a b))
    (hZright : ∀ t ∈ Set.Ico a b, HasDerivWithinAt Z
      (PhaseFlow.phaseField (normalAccel (I := I) Y x) (Z t))
      (Set.Ici t) t) :
    Geodesic.IsGeodesicOn (I := 𝓘(Real, E))
      (normalTotal (I := I) Y x) (fun t ↦ (Z t).1) (Set.Ioo a b) := by
  apply normalGeoOn_of_phase (I := I) Y x isOpen_Ioo
  intro t ht
  exact hasDerivAt_of_right hab hZcont hfield hZright ht



theorem normalFlow_contDiff
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (x : Y.M) {Z : Real → E × E} {a b : Real} (hab : a < b)
    (hZcont : ContinuousOn Z (Set.Icc a b))
    (hZright : ∀ t ∈ Set.Ico a b, HasDerivWithinAt Z
      (PhaseFlow.phaseField (normalAccel (I := I) Y x) (Z t))
      (Set.Ici t) t) :
    ContDiffOn Real ∞ Z (Set.Ioo a b) :=
  contDiffOn_of_right hab (normalPhase_contDiff (I := I) Y x) hZcont hZright



theorem normalFlow_geoOn
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (h : NormalCoordMetricBoundInput (I := I) X)
    (k : Nat) (x : (X.obj k).M) {r : Real}
    (hrMetric : Metric.ball (0 : E) r ⊆
      Metric.ball (0 : E) (h.radius k x))
    (hrQuarter :
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
      letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
      letI : T2Space (TangentBundle I (X.obj k).M) :=
        (X.obj k).t2TangentBundle
      Metric.ball (0 : E) r ⊆ Metric.ball (0 : E)
        (expMapC2Radius (I := I) (X.obj k).metric x / 4))
    (R : NNReal) {Z : Real → E × E}
    (hZcont : ContinuousOn Z (Set.Icc 0 1))
    (hZright : ∀ t ∈ Set.Ico 0 1, HasDerivWithinAt Z
      (PhaseFlow.phaseField (normalAccel (I := I) (X.obj k) x) (Z t))
      (Set.Ici t) t)
    (hZmem : ∀ t ∈ Set.Icc 0 1, Z t ∈ normalPhaseBox r R) :
    Geodesic.IsGeodesicOn (I := 𝓘(Real, E))
      (normalTotal (I := I) (X.obj k) x) (fun t ↦ (Z t).1)
      (Set.Ioo 0 1) := by
  have hacc : ContinuousOn
      (fun t ↦ normalAccel (I := I) (X.obj k) x (Z t)) (Set.Icc 0 1) :=
    (normalAccel_lip (I := I) h k x hrMetric hrQuarter R).continuousOn.comp
      hZcont hZmem
  have hfield : ContinuousOn
      (fun t ↦ PhaseFlow.phaseField
        (normalAccel (I := I) (X.obj k) x) (Z t)) (Set.Icc 0 1) := by
    simpa only [PhaseFlow.phaseField] using hZcont.snd.prodMk hacc
  exact normalGeoOn_of_right (I := I) (X.obj k) x zero_lt_one
    hZcont hfield hZright

end HCGCompactness
end DifferentialGeometry
