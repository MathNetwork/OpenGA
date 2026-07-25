import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepBTransition

set_option autoImplicit false
set_option linter.style.longLine false










noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Filter Topology

section HCGNormalTransition

open Bundle
open scoped Manifold ContDiff Bundle
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Geometry.Riemannian.Exponential

variable {E : Type uE} [NormedAddCommGroup E]
variable [InnerProductSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]





theorem existsTransRefH6
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (metricInput : NormalCoordMetricBoundInput (I := I) X)
    (phi0 : Nat -> Nat) (hphi0 : StrictMono phi0)
    (x y : ∀ k : Nat, (X.obj (phi0 k)).M)
    {U V Ua Va : Set E}
    (hU : IsOpen U) (hV : IsOpen V) (hUa : IsOpen Ua) (hVa : IsOpen Va)
    (hUanorm : ∃ Z : Real, ∀ z ∈ Ua, ‖z‖ ≤ Z)
    (hVanorm : ∃ Z : Real, ∀ z ∈ Va, ‖z‖ ≤ Z)
    (hUmetric : ∀ k,
      U ⊆ Metric.ball (0 : E) (metricInput.radius (phi0 k) (x k)))
    (hVmetric : ∀ k,
      V ⊆ Metric.ball (0 : E) (metricInput.radius (phi0 k) (y k)))
    (hUametric : ∀ k,
      Ua ⊆ Metric.ball (0 : E) (metricInput.radius (phi0 k) (x k)))
    (hVametric : ∀ k,
      Va ⊆ Metric.ball (0 : E) (metricInput.radius (phi0 k) (y k)))
    (hUexp : ∀ k,
      letI : TopologicalSpace (X.obj (phi0 k)).M := (X.obj (phi0 k)).topology
      letI : ChartedSpace H (X.obj (phi0 k)).M := (X.obj (phi0 k)).charted
      letI : IsManifold I ∞ (X.obj (phi0 k)).M := (X.obj (phi0 k)).smooth
      letI : T2Space (TangentBundle I (X.obj (phi0 k)).M) :=
        (X.obj (phi0 k)).t2TangentBundle
      U ⊆ Metric.ball (0 : E)
        (expMapC2Radius (I := I) (X.obj (phi0 k)).metric (x k)))
    (hVexp : ∀ k,
      letI : TopologicalSpace (X.obj (phi0 k)).M := (X.obj (phi0 k)).topology
      letI : ChartedSpace H (X.obj (phi0 k)).M := (X.obj (phi0 k)).charted
      letI : IsManifold I ∞ (X.obj (phi0 k)).M := (X.obj (phi0 k)).smooth
      letI : T2Space (TangentBundle I (X.obj (phi0 k)).M) :=
        (X.obj (phi0 k)).t2TangentBundle
      V ⊆ Metric.ball (0 : E)
        (expMapC2Radius (I := I) (X.obj (phi0 k)).metric (y k)))
    (hUaexp : ∀ k,
      letI : TopologicalSpace (X.obj (phi0 k)).M := (X.obj (phi0 k)).topology
      letI : ChartedSpace H (X.obj (phi0 k)).M := (X.obj (phi0 k)).charted
      letI : IsManifold I ∞ (X.obj (phi0 k)).M := (X.obj (phi0 k)).smooth
      letI : T2Space (TangentBundle I (X.obj (phi0 k)).M) :=
        (X.obj (phi0 k)).t2TangentBundle
      Ua ⊆ Metric.ball (0 : E)
        (expMapC2Radius (I := I) (X.obj (phi0 k)).metric (x k)))
    (hVaexp : ∀ k,
      letI : TopologicalSpace (X.obj (phi0 k)).M := (X.obj (phi0 k)).topology
      letI : ChartedSpace H (X.obj (phi0 k)).M := (X.obj (phi0 k)).charted
      letI : IsManifold I ∞ (X.obj (phi0 k)).M := (X.obj (phi0 k)).smooth
      letI : T2Space (TangentBundle I (X.obj (phi0 k)).M) :=
        (X.obj (phi0 k)).t2TangentBundle
      Va ⊆ Metric.ball (0 : E)
        (expMapC2Radius (I := I) (X.obj (phi0 k)).metric (y k)))
    (hJ : ∀ k, ContDiffOn Real (⊤ : ℕ∞)
      (normalTransition (I := I) (X.obj (phi0 k)) (x k) (y k)) U)
    (hJbar : ∀ k, ContDiffOn Real (⊤ : ℕ∞)
      (normalTransition (I := I) (X.obj (phi0 k)) (y k) (x k)) V)
    (hovlJ : ∀ k,
      NormalOverlapOn (I := I) (X.obj (phi0 k)) (x k) (y k) U)
    (hovlJbar : ∀ k,
      NormalOverlapOn (I := I) (X.obj (phi0 k)) (y k) (x k) V)
    (hmapJ : ∀ k, Set.MapsTo
      (normalTransition (I := I) (X.obj (phi0 k)) (x k) (y k)) U Va)
    (hmapJbar : ∀ k, Set.MapsTo
      (normalTransition (I := I) (X.obj (phi0 k)) (y k) (x k)) V Ua)
    (hLeft : ∀ k, ∀ z ∈ U,
      normalTransition (I := I) (X.obj (phi0 k)) (y k) (x k)
        (normalTransition (I := I) (X.obj (phi0 k)) (x k) (y k) z) = z)
    (hRight : ∀ k, ∀ w ∈ V,
      normalTransition (I := I) (X.obj (phi0 k)) (x k) (y k)
        (normalTransition (I := I) (X.obj (phi0 k)) (y k) (x k) w) = w) :
    ∃ (φ : Nat -> Nat) (Jinf : E -> E) (Jbarinf : E -> E),
      StrictMono φ ∧ StrictMono (phi0 ∘ φ) ∧
        ContDiffOn Real (⊤ : ℕ∞) Jinf U ∧
        ContDiffOn Real (⊤ : ℕ∞) Jbarinf V ∧
        MapCInfConvOnCompacts U
          (fun k => normalTransition (I := I) (X.obj (phi0 (φ k)))
            (x (φ k)) (y (φ k))) Jinf ∧
        MapCInfConvOnCompacts V
          (fun k => normalTransition (I := I) (X.obj (phi0 (φ k)))
            (y (φ k)) (x (φ k))) Jbarinf ∧
        (∀ z ∈ U, Jinf z ∈ V -> Jbarinf (Jinf z) = z) ∧
        (∀ w ∈ V, Jbarinf w ∈ U -> Jinf (Jbarinf w) = w) := by
  obtain ⟨φ, Jinf, Jbarinf, hφ, hJinf, hJbarinf, hconv, hconvbar,
      hleft, hright⟩ :=
    exists_trans_h6 (I := I) (X := X.subseq phi0)
      (NormalCoordMetricBoundInput.subseq (I := I) metricInput phi0)
      x y hU hV hUa hVa hUanorm hVanorm
      hUmetric hVmetric hUametric hVametric hUexp hVexp hUaexp hVaexp
      hJ hJbar hovlJ hovlJbar hmapJ hmapJbar hLeft hRight
  refine ⟨φ, Jinf, Jbarinf, hφ, hphi0.comp hφ, hJinf, hJbarinf, ?_, ?_,
    hleft, hright⟩
  · simpa [PointedRiemannianSeq.subseq] using hconv
  · simpa [PointedRiemannianSeq.subseq] using hconvbar






theorem existsTransFinite
    {ι : Type*} (s : Finset ι)
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (metricInput : NormalCoordMetricBoundInput (I := I) X)
    (x y : ι -> forall k : Nat, (X.obj k).M)
    (U V Ua Va : ι -> Set E)
    (hU : forall i, i ∈ s -> IsOpen (U i))
    (hV : forall i, i ∈ s -> IsOpen (V i))
    (hUa : forall i, i ∈ s -> IsOpen (Ua i))
    (hVa : forall i, i ∈ s -> IsOpen (Va i))
    (hUanorm : forall i, i ∈ s -> ∃ Z : Real, ∀ z ∈ Ua i, ‖z‖ ≤ Z)
    (hVanorm : forall i, i ∈ s -> ∃ Z : Real, ∀ z ∈ Va i, ‖z‖ ≤ Z)
    (hUmetric : forall i, i ∈ s -> forall k,
      U i ⊆ Metric.ball (0 : E) (metricInput.radius k (x i k)))
    (hVmetric : forall i, i ∈ s -> forall k,
      V i ⊆ Metric.ball (0 : E) (metricInput.radius k (y i k)))
    (hUametric : forall i, i ∈ s -> forall k,
      Ua i ⊆ Metric.ball (0 : E) (metricInput.radius k (x i k)))
    (hVametric : forall i, i ∈ s -> forall k,
      Va i ⊆ Metric.ball (0 : E) (metricInput.radius k (y i k)))
    (hUexp : forall i, i ∈ s -> forall k,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
      letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
      letI : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
      U i ⊆ Metric.ball (0 : E)
        (expMapC2Radius (I := I) (X.obj k).metric (x i k)))
    (hVexp : forall i, i ∈ s -> forall k,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
      letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
      letI : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
      V i ⊆ Metric.ball (0 : E)
        (expMapC2Radius (I := I) (X.obj k).metric (y i k)))
    (hUaexp : forall i, i ∈ s -> forall k,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
      letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
      letI : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
      Ua i ⊆ Metric.ball (0 : E)
        (expMapC2Radius (I := I) (X.obj k).metric (x i k)))
    (hVaexp : forall i, i ∈ s -> forall k,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
      letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
      letI : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
      Va i ⊆ Metric.ball (0 : E)
        (expMapC2Radius (I := I) (X.obj k).metric (y i k)))
    (hJ : forall i, i ∈ s -> forall k, ContDiffOn Real (⊤ : ℕ∞)
      (normalTransition (I := I) (X.obj k) (x i k) (y i k)) (U i))
    (hJbar : forall i, i ∈ s -> forall k, ContDiffOn Real (⊤ : ℕ∞)
      (normalTransition (I := I) (X.obj k) (y i k) (x i k)) (V i))
    (hovlJ : forall i, i ∈ s -> forall k,
      NormalOverlapOn (I := I) (X.obj k) (x i k) (y i k) (U i))
    (hovlJbar : forall i, i ∈ s -> forall k,
      NormalOverlapOn (I := I) (X.obj k) (y i k) (x i k) (V i))
    (hmapJ : forall i, i ∈ s -> forall k, Set.MapsTo
      (normalTransition (I := I) (X.obj k) (x i k) (y i k)) (U i) (Va i))
    (hmapJbar : forall i, i ∈ s -> forall k, Set.MapsTo
      (normalTransition (I := I) (X.obj k) (y i k) (x i k)) (V i) (Ua i))
    (hLeft : forall i, i ∈ s -> forall k, forall z, z ∈ U i ->
      normalTransition (I := I) (X.obj k) (y i k) (x i k)
        (normalTransition (I := I) (X.obj k) (x i k) (y i k) z) = z)
    (hRight : forall i, i ∈ s -> forall k, forall w, w ∈ V i ->
      normalTransition (I := I) (X.obj k) (x i k) (y i k)
        (normalTransition (I := I) (X.obj k) (y i k) (x i k) w) = w) :
    exists phi : Nat -> Nat, StrictMono phi /\
      forall i, i ∈ s -> exists Jinf : E -> E, exists Jbarinf : E -> E,
        ContDiffOn Real (⊤ : ℕ∞) Jinf (U i) /\
        ContDiffOn Real (⊤ : ℕ∞) Jbarinf (V i) /\
        MapCInfConvOnCompacts (U i)
          (fun k => normalTransition (I := I) (X.obj (phi k))
            (x i (phi k)) (y i (phi k))) Jinf /\
        MapCInfConvOnCompacts (V i)
          (fun k => normalTransition (I := I) (X.obj (phi k))
            (y i (phi k)) (x i (phi k))) Jbarinf /\
        (forall z, z ∈ U i -> Jinf z ∈ V i -> Jbarinf (Jinf z) = z) /\
        (forall w, w ∈ V i -> Jbarinf w ∈ U i -> Jinf (Jbarinf w) = w) := by
  classical
  revert hU hV hUa hVa hUanorm hVanorm hUmetric hVmetric hUametric hVametric
    hUexp hVexp hUaexp hVaexp hJ hJbar hovlJ hovlJbar hmapJ hmapJbar hLeft hRight
  induction s using Finset.induction with
  | empty =>
      intro hU hV hUa hVa hUanorm hVanorm hUmetric hVmetric hUametric hVametric
        hUexp hVexp hUaexp hVaexp hJ hJbar hovlJ hovlJbar hmapJ hmapJbar
        hLeft hRight
      exact ⟨id, strictMono_id, fun i hi => by simp at hi⟩
  | @insert a s ha IH =>
      intro hU hV hUa hVa hUanorm hVanorm hUmetric hVmetric hUametric hVametric
        hUexp hVexp hUaexp hVaexp hJ hJbar hovlJ hovlJbar hmapJ hmapJbar
        hLeft hRight
      obtain ⟨phi0, hphi0, hprev⟩ :=
        IH
          (fun i hi => hU i (Finset.mem_insert_of_mem hi))
          (fun i hi => hV i (Finset.mem_insert_of_mem hi))
          (fun i hi => hUa i (Finset.mem_insert_of_mem hi))
          (fun i hi => hVa i (Finset.mem_insert_of_mem hi))
          (fun i hi => hUanorm i (Finset.mem_insert_of_mem hi))
          (fun i hi => hVanorm i (Finset.mem_insert_of_mem hi))
          (fun i hi => hUmetric i (Finset.mem_insert_of_mem hi))
          (fun i hi => hVmetric i (Finset.mem_insert_of_mem hi))
          (fun i hi => hUametric i (Finset.mem_insert_of_mem hi))
          (fun i hi => hVametric i (Finset.mem_insert_of_mem hi))
          (fun i hi => hUexp i (Finset.mem_insert_of_mem hi))
          (fun i hi => hVexp i (Finset.mem_insert_of_mem hi))
          (fun i hi => hUaexp i (Finset.mem_insert_of_mem hi))
          (fun i hi => hVaexp i (Finset.mem_insert_of_mem hi))
          (fun i hi => hJ i (Finset.mem_insert_of_mem hi))
          (fun i hi => hJbar i (Finset.mem_insert_of_mem hi))
          (fun i hi => hovlJ i (Finset.mem_insert_of_mem hi))
          (fun i hi => hovlJbar i (Finset.mem_insert_of_mem hi))
          (fun i hi => hmapJ i (Finset.mem_insert_of_mem hi))
          (fun i hi => hmapJbar i (Finset.mem_insert_of_mem hi))
          (fun i hi => hLeft i (Finset.mem_insert_of_mem hi))
          (fun i hi => hRight i (Finset.mem_insert_of_mem hi))
      obtain ⟨phi1, Jinf, Jbarinf, hphi1, hcomp, hJinf, hJbarinf, hJ, hJbar,
          hleft, hright⟩ :=
        existsTransRefH6 (I := I) metricInput phi0 hphi0
          (fun k => x a (phi0 k)) (fun k => y a (phi0 k))
          (hU a (Finset.mem_insert_self a s)) (hV a (Finset.mem_insert_self a s))
          (hUa a (Finset.mem_insert_self a s)) (hVa a (Finset.mem_insert_self a s))
          (hUanorm a (Finset.mem_insert_self a s))
          (hVanorm a (Finset.mem_insert_self a s))
          (fun k => hUmetric a (Finset.mem_insert_self a s) (phi0 k))
          (fun k => hVmetric a (Finset.mem_insert_self a s) (phi0 k))
          (fun k => hUametric a (Finset.mem_insert_self a s) (phi0 k))
          (fun k => hVametric a (Finset.mem_insert_self a s) (phi0 k))
          (fun k => hUexp a (Finset.mem_insert_self a s) (phi0 k))
          (fun k => hVexp a (Finset.mem_insert_self a s) (phi0 k))
          (fun k => hUaexp a (Finset.mem_insert_self a s) (phi0 k))
          (fun k => hVaexp a (Finset.mem_insert_self a s) (phi0 k))
          (fun k => hJ a (Finset.mem_insert_self a s) (phi0 k))
          (fun k => hJbar a (Finset.mem_insert_self a s) (phi0 k))
          (fun k => hovlJ a (Finset.mem_insert_self a s) (phi0 k))
          (fun k => hovlJbar a (Finset.mem_insert_self a s) (phi0 k))
          (fun k => hmapJ a (Finset.mem_insert_self a s) (phi0 k))
          (fun k => hmapJbar a (Finset.mem_insert_self a s) (phi0 k))
          (fun k z hz => hLeft a (Finset.mem_insert_self a s) (phi0 k) z hz)
          (fun k w hw => hRight a (Finset.mem_insert_self a s) (phi0 k) w hw)
      refine ⟨phi0 ∘ phi1, hcomp, fun i hi => ?_⟩
      rcases Finset.mem_insert.mp hi with rfl | his
      · refine ⟨Jinf, Jbarinf, hJinf, hJbarinf, ?_, ?_, hleft, hright⟩
        · simpa [Function.comp_apply] using hJ
        · simpa [Function.comp_apply] using hJbar
      · obtain ⟨Jprev, Jbarprev, hJprev, hJbarprev, hconv, hconvbar,
            hleftprev, hrightprev⟩ := hprev i his
        refine ⟨Jprev, Jbarprev, hJprev, hJbarprev, ?_, ?_, hleftprev, hrightprev⟩
        · simpa [Function.comp_apply] using hconv.comp_subseq hphi1
        · simpa [Function.comp_apply] using hconvbar.comp_subseq hphi1








theorem existsTransUniv
    {ι : Type*} [Finite ι]
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (metricInput : NormalCoordMetricBoundInput (I := I) X)
    (x y : ι -> forall k : Nat, (X.obj k).M)
    (U V Ua Va : ι -> Set E)
    (hU : forall i, IsOpen (U i))
    (hV : forall i, IsOpen (V i))
    (hUa : forall i, IsOpen (Ua i))
    (hVa : forall i, IsOpen (Va i))
    (hUanorm : forall i, ∃ Z : Real, ∀ z ∈ Ua i, ‖z‖ ≤ Z)
    (hVanorm : forall i, ∃ Z : Real, ∀ z ∈ Va i, ‖z‖ ≤ Z)
    (hUmetric : forall i k,
      U i ⊆ Metric.ball (0 : E) (metricInput.radius k (x i k)))
    (hVmetric : forall i k,
      V i ⊆ Metric.ball (0 : E) (metricInput.radius k (y i k)))
    (hUametric : forall i k,
      Ua i ⊆ Metric.ball (0 : E) (metricInput.radius k (x i k)))
    (hVametric : forall i k,
      Va i ⊆ Metric.ball (0 : E) (metricInput.radius k (y i k)))
    (hUexp : forall i k,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
      letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
      letI : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
      U i ⊆ Metric.ball (0 : E)
        (expMapC2Radius (I := I) (X.obj k).metric (x i k)))
    (hVexp : forall i k,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
      letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
      letI : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
      V i ⊆ Metric.ball (0 : E)
        (expMapC2Radius (I := I) (X.obj k).metric (y i k)))
    (hUaexp : forall i k,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
      letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
      letI : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
      Ua i ⊆ Metric.ball (0 : E)
        (expMapC2Radius (I := I) (X.obj k).metric (x i k)))
    (hVaexp : forall i k,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
      letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
      letI : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
      Va i ⊆ Metric.ball (0 : E)
        (expMapC2Radius (I := I) (X.obj k).metric (y i k)))
    (hJ : forall i k, ContDiffOn Real (⊤ : ℕ∞)
      (normalTransition (I := I) (X.obj k) (x i k) (y i k)) (U i))
    (hJbar : forall i k, ContDiffOn Real (⊤ : ℕ∞)
      (normalTransition (I := I) (X.obj k) (y i k) (x i k)) (V i))
    (hovlJ : forall i, forall k,
      NormalOverlapOn (I := I) (X.obj k) (x i k) (y i k) (U i))
    (hovlJbar : forall i, forall k,
      NormalOverlapOn (I := I) (X.obj k) (y i k) (x i k) (V i))
    (hmapJ : forall i k, Set.MapsTo
      (normalTransition (I := I) (X.obj k) (x i k) (y i k)) (U i) (Va i))
    (hmapJbar : forall i k, Set.MapsTo
      (normalTransition (I := I) (X.obj k) (y i k) (x i k)) (V i) (Ua i))
    (hLeft : forall i, forall k, forall z, z ∈ U i ->
      normalTransition (I := I) (X.obj k) (y i k) (x i k)
        (normalTransition (I := I) (X.obj k) (x i k) (y i k) z) = z)
    (hRight : forall i, forall k, forall w, w ∈ V i ->
      normalTransition (I := I) (X.obj k) (x i k) (y i k)
        (normalTransition (I := I) (X.obj k) (y i k) (x i k) w) = w) :
    exists phi : Nat -> Nat, StrictMono phi /\
      exists Jinf : ι -> E -> E, exists Jbarinf : ι -> E -> E,
        forall i,
          ContDiffOn Real (⊤ : ℕ∞) (Jinf i) (U i) /\
          ContDiffOn Real (⊤ : ℕ∞) (Jbarinf i) (V i) /\
          ContinuousOn (Jinf i) (U i) /\
          ContinuousOn (Jbarinf i) (V i) /\
          MapCInfConvOnCompacts (U i)
            (fun k => normalTransition (I := I) (X.obj (phi k))
              (x i (phi k)) (y i (phi k))) (Jinf i) /\
          MapCInfConvOnCompacts (V i)
            (fun k => normalTransition (I := I) (X.obj (phi k))
              (y i (phi k)) (x i (phi k))) (Jbarinf i) /\
          (forall z, z ∈ U i -> Jinf i z ∈ V i -> Jbarinf i (Jinf i z) = z) /\
          (forall w, w ∈ V i -> Jbarinf i w ∈ U i -> Jinf i (Jbarinf i w) = w) := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  obtain ⟨phi, hphi, hlim⟩ :=
    existsTransFinite (I := I) (Finset.univ : Finset ι) metricInput x y U V Ua Va
      (fun i _ => hU i) (fun i _ => hV i)
      (fun i _ => hUa i) (fun i _ => hVa i)
      (fun i _ => hUanorm i) (fun i _ => hVanorm i)
      (fun i _ => hUmetric i) (fun i _ => hVmetric i)
      (fun i _ => hUametric i) (fun i _ => hVametric i)
      (fun i _ => hUexp i) (fun i _ => hVexp i)
      (fun i _ => hUaexp i) (fun i _ => hVaexp i)
      (fun i _ => hJ i) (fun i _ => hJbar i)
      (fun i _ => hovlJ i) (fun i _ => hovlJbar i)
      (fun i _ => hmapJ i) (fun i _ => hmapJbar i)
      (fun i _ => hLeft i) (fun i _ => hRight i)
  let Jinf : ι -> E -> E := fun i =>
    let hi : i ∈ (Finset.univ : Finset ι) := Finset.mem_univ i
    Classical.choose (hlim i hi)
  let Jbarinf : ι -> E -> E := fun i =>
    let hi : i ∈ (Finset.univ : Finset ι) := Finset.mem_univ i
    Classical.choose (Classical.choose_spec (hlim i hi))
  refine ⟨phi, hphi, Jinf, Jbarinf, fun i => ?_⟩
  let hi : i ∈ (Finset.univ : Finset ι) := Finset.mem_univ i
  have hspec :
      ContDiffOn Real (⊤ : ℕ∞) (Classical.choose (hlim i hi)) (U i) ∧
      ContDiffOn Real (⊤ : ℕ∞)
        (Classical.choose (Classical.choose_spec (hlim i hi))) (V i) ∧
      MapCInfConvOnCompacts (U i)
        (fun k => normalTransition (I := I) (X.obj (phi k))
          (x i (phi k)) (y i (phi k))) (Classical.choose (hlim i hi)) ∧
      MapCInfConvOnCompacts (V i)
        (fun k => normalTransition (I := I) (X.obj (phi k))
          (y i (phi k)) (x i (phi k)))
        (Classical.choose (Classical.choose_spec (hlim i hi))) ∧
      (forall z, z ∈ U i ->
        Classical.choose (hlim i hi) z ∈ V i ->
          Classical.choose (Classical.choose_spec (hlim i hi))
            (Classical.choose (hlim i hi) z) = z) ∧
      (forall w, w ∈ V i ->
        Classical.choose (Classical.choose_spec (hlim i hi)) w ∈ U i ->
          Classical.choose (hlim i hi)
            (Classical.choose (Classical.choose_spec (hlim i hi)) w) = w) :=
    Classical.choose_spec (Classical.choose_spec (hlim i hi))
  rcases hspec with ⟨hJinf, hJbarinf, hconv, hconvbar, hleft, hright⟩
  have hJcont : ContinuousOn (Classical.choose (hlim i hi)) (U i) :=
    hJinf.continuousOn
  have hJbarcont :
      ContinuousOn (Classical.choose (Classical.choose_spec (hlim i hi))) (V i) :=
    hJbarinf.continuousOn
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [Jinf] using hJinf
  · simpa [Jbarinf] using hJbarinf
  · simpa [Jinf] using hJcont
  · simpa [Jbarinf] using hJbarcont
  · simpa [Jinf] using hconv
  · simpa [Jbarinf] using hconvbar
  · intro z hz hzV
    dsimp [Jinf, Jbarinf] at hzV ⊢
    exact hleft z hz hzV
  · intro w hw hwU
    dsimp [Jinf, Jbarinf] at hwU ⊢
    exact hright w hw hwU







structure NormalTransAt
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)} {ι : Type*}
    (metricInput : NormalCoordMetricBoundInput (I := I) X)
    (x y : ι → ∀ k : Nat, (X.obj k).M)
    (U V Ua Va : ι → Set E) (i : ι) (k : Nat) : Prop where
  Umetric : U i ⊆ Metric.ball (0 : E) (metricInput.radius k (x i k))
  Vmetric : V i ⊆ Metric.ball (0 : E) (metricInput.radius k (y i k))
  Uametric : Ua i ⊆ Metric.ball (0 : E) (metricInput.radius k (x i k))
  Vametric : Va i ⊆ Metric.ball (0 : E) (metricInput.radius k (y i k))
  Uexp :
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
    letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    letI : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
    U i ⊆ Metric.ball (0 : E)
      (expMapC2Radius (I := I) (X.obj k).metric (x i k))
  Vexp :
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
    letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    letI : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
    V i ⊆ Metric.ball (0 : E)
      (expMapC2Radius (I := I) (X.obj k).metric (y i k))
  Uaexp :
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
    letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    letI : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
    Ua i ⊆ Metric.ball (0 : E)
      (expMapC2Radius (I := I) (X.obj k).metric (x i k))
  Vaexp :
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
    letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    letI : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
    Va i ⊆ Metric.ball (0 : E)
      (expMapC2Radius (I := I) (X.obj k).metric (y i k))
  J : ContDiffOn Real (⊤ : ℕ∞)
    (normalTransition (I := I) (X.obj k) (x i k) (y i k)) (U i)
  Jbar : ContDiffOn Real (⊤ : ℕ∞)
    (normalTransition (I := I) (X.obj k) (y i k) (x i k)) (V i)
  ovlJ : NormalOverlapOn (I := I) (X.obj k) (x i k) (y i k) (U i)
  ovlJbar : NormalOverlapOn (I := I) (X.obj k) (y i k) (x i k) (V i)
  mapJ : Set.MapsTo
    (normalTransition (I := I) (X.obj k) (x i k) (y i k)) (U i) (Va i)
  mapJbar : Set.MapsTo
    (normalTransition (I := I) (X.obj k) (y i k) (x i k)) (V i) (Ua i)
  left : ∀ z, z ∈ U i →
    normalTransition (I := I) (X.obj k) (y i k) (x i k)
      (normalTransition (I := I) (X.obj k) (x i k) (y i k) z) = z
  right : ∀ w, w ∈ V i →
    normalTransition (I := I) (X.obj k) (x i k) (y i k)
      (normalTransition (I := I) (X.obj k) (y i k) (x i k) w) = w





theorem existsTransTail
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)} {ι : Type*} [Finite ι]
    (metricInput : NormalCoordMetricBoundInput (I := I) X)
    (x y : ι → ∀ k : Nat, (X.obj k).M)
    (U V Ua Va : ι → Set E)
    (hU : ∀ i, IsOpen (U i)) (hV : ∀ i, IsOpen (V i))
    (hUa : ∀ i, IsOpen (Ua i)) (hVa : ∀ i, IsOpen (Va i))
    (hUanorm : ∀ i, ∃ Z : Real, ∀ z ∈ Ua i, ‖z‖ ≤ Z)
    (hVanorm : ∀ i, ∃ Z : Real, ∀ z ∈ Va i, ‖z‖ ≤ Z)
    (htail : ∀ i, ∀ᶠ k in atTop,
      NormalTransAt (I := I) metricInput x y U V Ua Va i k) :
    ∃ phi : Nat → Nat, StrictMono phi ∧
      ∃ Jinf : ι → E → E, ∃ Jbarinf : ι → E → E,
        ∀ i,
          ContDiffOn Real (⊤ : ℕ∞) (Jinf i) (U i) ∧
          ContDiffOn Real (⊤ : ℕ∞) (Jbarinf i) (V i) ∧
          ContinuousOn (Jinf i) (U i) ∧
          ContinuousOn (Jbarinf i) (V i) ∧
          MapCInfConvOnCompacts (U i)
            (fun k => normalTransition (I := I) (X.obj (phi k))
              (x i (phi k)) (y i (phi k))) (Jinf i) ∧
          MapCInfConvOnCompacts (V i)
            (fun k => normalTransition (I := I) (X.obj (phi k))
              (y i (phi k)) (x i (phi k))) (Jbarinf i) ∧
          (∀ z, z ∈ U i → Jinf i z ∈ V i → Jbarinf i (Jinf i z) = z) ∧
          (∀ w, w ∈ V i → Jbarinf i w ∈ U i → Jinf i (Jbarinf i w) = w) := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  have hall : ∀ᶠ k in atTop, ∀ i : ι,
      NormalTransAt (I := I) metricInput x y U V Ua Va i k :=
    Filter.eventually_all.mpr htail
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hall
  let tau : Nat → Nat := fun k => k + N
  have htau : StrictMono tau := by
    simpa only [tau] using strictMono_id.add_const N
  have hdata (k : Nat) (i : ι) :=
    hN (tau k) (by simpa only [tau] using Nat.le_add_left N k) i
  let xt : ι → ∀ k : Nat, ((X.subseq tau).obj k).M :=
    fun i k => x i (tau k)
  let yt : ι → ∀ k : Nat, ((X.subseq tau).obj k).M :=
    fun i k => y i (tau k)
  obtain ⟨phi1, hphi1, Jinf, Jbarinf, hspec⟩ :=
    existsTransUniv (I := I) (X := X.subseq tau)
      (NormalCoordMetricBoundInput.subseq (I := I) metricInput tau)
      xt yt U V Ua Va hU hV hUa hVa hUanorm hVanorm
      (fun i k => by
        simpa only [NormalCoordMetricBoundInput.subseq, xt] using (hdata k i).Umetric)
      (fun i k => by
        simpa only [NormalCoordMetricBoundInput.subseq, yt] using (hdata k i).Vmetric)
      (fun i k => by
        simpa only [NormalCoordMetricBoundInput.subseq, xt] using (hdata k i).Uametric)
      (fun i k => by
        simpa only [NormalCoordMetricBoundInput.subseq, yt] using (hdata k i).Vametric)
      (fun i k => by
        simpa only [PointedRiemannianSeq.subseq, xt] using (hdata k i).Uexp)
      (fun i k => by
        simpa only [PointedRiemannianSeq.subseq, yt] using (hdata k i).Vexp)
      (fun i k => by
        simpa only [PointedRiemannianSeq.subseq, xt] using (hdata k i).Uaexp)
      (fun i k => by
        simpa only [PointedRiemannianSeq.subseq, yt] using (hdata k i).Vaexp)
      (fun i k => by
        simpa only [PointedRiemannianSeq.subseq, xt, yt] using (hdata k i).J)
      (fun i k => by
        simpa only [PointedRiemannianSeq.subseq, xt, yt] using (hdata k i).Jbar)
      (fun i k => by
        simpa only [PointedRiemannianSeq.subseq, xt, yt] using (hdata k i).ovlJ)
      (fun i k => by
        simpa only [PointedRiemannianSeq.subseq, xt, yt] using (hdata k i).ovlJbar)
      (fun i k => by
        simpa only [PointedRiemannianSeq.subseq, xt, yt] using (hdata k i).mapJ)
      (fun i k => by
        simpa only [PointedRiemannianSeq.subseq, xt, yt] using (hdata k i).mapJbar)
      (fun i k => by
        simpa only [PointedRiemannianSeq.subseq, xt, yt] using (hdata k i).left)
      (fun i k => by
        simpa only [PointedRiemannianSeq.subseq, xt, yt] using (hdata k i).right)
  let phi : Nat → Nat := tau ∘ phi1
  have hphi : StrictMono phi := by
    simpa only [phi] using htau.comp hphi1
  refine ⟨phi, hphi, Jinf, Jbarinf, fun i => ?_⟩
  refine ⟨(hspec i).1, (hspec i).2.1, (hspec i).2.2.1,
    (hspec i).2.2.2.1, ?_, ?_, (hspec i).2.2.2.2.2.2.1,
    (hspec i).2.2.2.2.2.2.2⟩
  · simpa only [PointedRiemannianSeq.subseq, xt, yt, phi,
      Function.comp_apply] using (hspec i).2.2.2.2.1
  · simpa only [PointedRiemannianSeq.subseq, xt, yt, phi,
      Function.comp_apply] using (hspec i).2.2.2.2.2.1

end HCGNormalTransition

end HCGCompactness
end DifferentialGeometry
