import DifferentialGeometry.Analysis.Calculus.MapConvergenceComp
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.NormalBranchCage
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepBLocalMetrics

set_option autoImplicit false










noncomputable section

open Filter Set Topology
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry
namespace HCGCompactness

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

namespace MetricCompactnessInputs



theorem exists_live_metric
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) (r : Real) :
    let R := 2 * inp.decay.lambda inp.D 0 * (inp.pack.A r : Real)
    ∃ (psi : Nat → Nat)
        (gInf : E →
          (LiveSlot L inp.pack r → (E →L[Real] E →L[Real] Real))),
      StrictMono psi ∧
      (∀ k (alpha : LiveSlot L inp.pack r),
        inp.decay.dist (L.φ (psi k))
          (seqCenterD inp.decay P L (psi k) (alpha.1 : Nat))
          (X.obj (L.φ (psi k))).basepoint ≤ R) ∧
      ContDiffOn Real (∞ : WithTop ℕ∞) gInf
        (Metric.ball 0 (inp.normalRadius.phaseRadius R)) ∧
      MapCInfConvOnCompacts
        (Metric.ball 0 (inp.normalRadius.phaseRadius R))
        (fun k z alpha ↦ normalCoordMetric (I := I)
          (X.obj (L.φ (psi k)))
          (seqCenterD inp.decay P L (psi k) (alpha.1 : Nat)) z)
        gInf ∧
      (∀ k, ContDiffOn Real (∞ : WithTop ℕ∞)
        (fun z (alpha : LiveSlot L inp.pack r) ↦ normalCoordMetric (I := I)
          (X.obj (L.φ (psi k)))
          (seqCenterD inp.decay P L (psi k) (alpha.1 : Nat)) z)
        (Metric.ball 0 (inp.normalRadius.phaseRadius R))) ∧
      ∀ z ∈ Metric.ball (0 : E) (inp.normalRadius.phaseRadius R),
        ∀ alpha v,
          (1 / 2 : Real) * ‖v‖ ^ 2 ≤ gInf z alpha v v ∧
            gInf z alpha v v ≤ 2 * ‖v‖ ^ 2 := by
  classical
  let R : Real := 2 * inp.decay.lambda inp.D 0 * (inp.pack.A r : Real)
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (liveCenters_cage inp.decay inp.hD P inp.realizes L inp.pack r)
  let shift : Nat → Nat := fun k ↦ k + N
  have hshift : StrictMono shift := by
    simpa only [shift] using strictMono_id.add_const N
  let index : Nat → Nat := fun k ↦ L.φ (shift k)
  let X' : PointedRiemannianSeq.{u, uE, uH} (I := I) := X.subseq index
  let input' : NormalCoordMetricBoundInput (I := I) X' :=
    inp.normalBounds.subseq index
  let c : LiveSlot L inp.pack r → ∀ k : Nat, (X'.obj k).M :=
    fun alpha k ↦ seqCenterD inp.decay P L (shift k) (alpha.1 : Nat)
  have hcenter : ∀ k alpha,
      inp.decay.dist (index k) (c alpha k) (X'.obj k).basepoint ≤ R := by
    intro k alpha
    exact hN (shift k) (by simp only [shift]; omega) alpha
  have hdom : ∀ k alpha,
      Metric.ball (0 : E) (inp.normalRadius.phaseRadius R) ⊆
        Metric.ball 0 (input'.radius k (c alpha k)) := by
    intro k alpha
    simpa only [input', X', index, c, PointedRiemannianSeq.subseq] using
      inp.normalRadius.phaseRadius_metric (hcenter k alpha)
  have hsub : ∀ k alpha,
      letI : TopologicalSpace (X'.obj k).M := (X'.obj k).topology
      letI : ChartedSpace H (X'.obj k).M := (X'.obj k).charted
      letI : IsManifold I ∞ (X'.obj k).M := (X'.obj k).smooth
      letI : T2Space (TangentBundle I (X'.obj k).M) :=
        (X'.obj k).t2TangentBundle
      Metric.ball (0 : E) (inp.normalRadius.phaseRadius R) ⊆
        Metric.ball 0
        (Geometry.Riemannian.expMapC2Radius
            (I := I) (X'.obj k).metric (c alpha k)) := by
    intro k alpha
    letI : TopologicalSpace (X'.obj k).M := (X'.obj k).topology
    letI : ChartedSpace H (X'.obj k).M := (X'.obj k).charted
    letI : IsManifold I ∞ (X'.obj k).M := (X'.obj k).smooth
    letI : T2Space (TangentBundle I (X'.obj k).M) :=
      (X'.obj k).t2TangentBundle
    have hquarter := inp.normalRadius.phaseRadius_exp (hcenter k alpha)
    have hquarter' : Metric.ball (0 : E) (inp.normalRadius.phaseRadius R) ⊆
        Metric.ball 0 (Geometry.Riemannian.expMapC2Radius
          (I := I) (X'.obj k).metric (c alpha k) / 4) := by
      simpa only [X', PointedRiemannianSeq.subseq] using hquarter
    exact hquarter'.trans (Metric.ball_subset_ball (by
      nlinarith [Geometry.Riemannian.expMapC2Radius_pos
        (I := I) (X'.obj k).metric (c alpha k)]))
  obtain ⟨phi, gInf, hphi, hgInf, hconv, hequiv⟩ :=
    exists_metric_lim_pi (I := I) input' c Metric.isOpen_ball hdom hsub
  let psi : Nat → Nat := fun k ↦ shift (phi k)
  have hpsi : StrictMono psi := hshift.comp hphi
  refine ⟨psi, gInf, hpsi, ?_, hgInf, ?_, ?_, hequiv⟩
  · intro k alpha
    simpa only [psi, c, index, X', PointedRiemannianSeq.subseq] using
      hcenter (phi k) alpha
  · simpa only [psi, X', input', index, c, PointedRiemannianSeq.subseq] using hconv
  · intro k
    refine contDiffOn_pi.mpr fun alpha ↦ ?_
    simpa only [psi, X', input', index, c, PointedRiemannianSeq.subseq] using
      (normalCoordMetric_contDiffOn_expBall
        (I := I) (X'.obj (phi k)) (c alpha (phi k))).mono (hsub (phi k) alpha)



theorem exists_slot_metric
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) (r : Real) :
    ∃ (psi : Nat → Nat)
        (gInf : LiveSlot L inp.pack r →
          E → (E →L[Real] E →L[Real] Real)),
      StrictMono psi ∧
      (∀ n (alpha : LiveSlot L inp.pack r),
        inp.decay.dist (L.φ (psi n))
          (seqCenterD inp.decay P L (psi n) (alpha.1 : Nat))
          (X.obj (L.φ (psi n))).basepoint ≤
            L.rInf (alpha.1 : Nat) + 1) ∧
      ∀ alpha : LiveSlot L inp.pack r,
        let Ralpha := L.rInf (alpha.1 : Nat) + 1
        let Ualpha := Metric.ball (0 : E)
          (inp.normalRadius.phaseRadius Ralpha)
        ContDiffOn Real (∞ : WithTop ℕ∞) (gInf alpha) Ualpha ∧
        MapCInfConvOnCompacts Ualpha
          (fun n => normalCoordMetric (I := I)
            (X.obj (L.φ (psi n)))
            (seqCenterD inp.decay P L (psi n) (alpha.1 : Nat)))
          (gInf alpha) ∧
        ∀ z ∈ Ualpha, ∀ v : E,
          (1 / 2 : Real) * ‖v‖ ^ 2 ≤ gInf alpha z v v ∧
            gInf alpha z v v ≤ 2 * ‖v‖ ^ 2 := by
  classical
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (liveCenters_rInf inp.decay P inp.realizes L inp.pack r)
  let shift : Nat → Nat := fun n => n + N
  have hshift : StrictMono shift := by
    simpa only [shift] using strictMono_id.add_const N
  let U : LiveSlot L inp.pack r → Set E := fun alpha =>
    Metric.ball 0
      (inp.normalRadius.phaseRadius (L.rInf (alpha.1 : Nat) + 1))
  let Φ : LiveSlot L inp.pack r → Nat → E →
      (E →L[Real] E →L[Real] Real) := fun alpha n z =>
    normalCoordMetric (I := I) (X.obj (L.φ (shift n)))
      (seqCenterD inp.decay P L (shift n) (alpha.1 : Nat)) z
  let Q : LiveSlot L inp.pack r →
      (E → (E →L[Real] E →L[Real] Real)) → Prop := fun alpha g =>
    ContDiffOn Real (∞ : WithTop ℕ∞) g (U alpha) ∧
      ∀ z ∈ U alpha, ∀ v : E,
        (1 / 2 : Real) * ‖v‖ ^ 2 ≤ g z v v ∧
          g z v v ≤ 2 * ‖v‖ ^ 2
  have hstep : ∀ alpha (τ : Nat → Nat), StrictMono τ →
      ∃ (σ : Nat → Nat) (g : E → (E →L[Real] E →L[Real] Real)),
        StrictMono σ ∧
        MapCInfConvOnCompacts (U alpha)
          (fun n => Φ alpha (τ (σ n))) g ∧ Q alpha g := by
    intro alpha τ hτ
    let index : Nat → Nat := fun n => L.φ (shift (τ n))
    let X' : PointedRiemannianSeq.{u, uE, uH} (I := I) := X.subseq index
    let input' : NormalCoordMetricBoundInput (I := I) X' :=
      inp.normalBounds.subseq index
    let c : ∀ n : Nat, (X'.obj n).M := fun n =>
      seqCenterD inp.decay P L (shift (τ n)) (alpha.1 : Nat)
    have hcenter : ∀ n,
        inp.decay.dist (index n) (c n) (X'.obj n).basepoint ≤
          L.rInf (alpha.1 : Nat) + 1 := by
      intro n
      have hn : N ≤ shift (τ n) := by simp only [shift]; omega
      exact (hN (shift (τ n)) hn alpha).le
    have hdom : ∀ n, U alpha ⊆
        Metric.ball (0 : E) (input'.radius n (c n)) := by
      intro n
      simpa only [U, input', X', index, c, PointedRiemannianSeq.subseq] using
        inp.normalRadius.phaseRadius_metric (hcenter n)
    have hsub : ∀ n,
        letI : TopologicalSpace (X'.obj n).M := (X'.obj n).topology
        letI : ChartedSpace H (X'.obj n).M := (X'.obj n).charted
        letI : IsManifold I ∞ (X'.obj n).M := (X'.obj n).smooth
        letI : T2Space (TangentBundle I (X'.obj n).M) :=
          (X'.obj n).t2TangentBundle
        U alpha ⊆ Metric.ball (0 : E)
          (Geometry.Riemannian.expMapC2Radius
            (I := I) (X'.obj n).metric (c n)) := by
      intro n
      letI : TopologicalSpace (X'.obj n).M := (X'.obj n).topology
      letI : ChartedSpace H (X'.obj n).M := (X'.obj n).charted
      letI : IsManifold I ∞ (X'.obj n).M := (X'.obj n).smooth
      letI : T2Space (TangentBundle I (X'.obj n).M) :=
        (X'.obj n).t2TangentBundle
      have hquarter := inp.normalRadius.phaseRadius_exp (hcenter n)
      have hquarter' : U alpha ⊆ Metric.ball (0 : E)
          (Geometry.Riemannian.expMapC2Radius
            (I := I) (X'.obj n).metric (c n) / 4) := by
        simpa only [U, X', index, c, PointedRiemannianSeq.subseq] using hquarter
      exact hquarter'.trans (Metric.ball_subset_ball (by
        nlinarith [Geometry.Riemannian.expMapC2Radius_pos
          (I := I) (X'.obj n).metric (c n)]))
    obtain ⟨σ, g, hσ, hg, hconv, hequiv⟩ :=
      exists_metricLimit_normalCoord (I := I) input' c Metric.isOpen_ball hdom hsub
    refine ⟨σ, g, hσ, ?_, ?_, hequiv⟩
    · simpa only [Φ, X', input', index, c, PointedRiemannianSeq.subseq] using hconv
    · simpa only [Q] using hg
  obtain ⟨psi0, hpsi0, hall⟩ :=
    exists_cInf_finite U Φ Q hstep
  choose gInf hconv hQ using hall
  let psi : Nat → Nat := shift ∘ psi0
  refine ⟨psi, gInf, hshift.comp hpsi0, ?_, ?_⟩
  · intro n alpha
    have hn : N ≤ shift (psi0 n) := by simp only [shift]; omega
    simpa only [psi, Function.comp_apply] using
      (hN (shift (psi0 n)) hn alpha).le
  intro alpha
  have hconvAlpha := hconv alpha
  have hQAlpha := hQ alpha
  dsimp only [Q] at hQAlpha
  refine ⟨?_, ?_, ?_⟩
  · simpa only [U] using hQAlpha.1
  · simpa only [U, Φ, psi, Function.comp_apply] using hconvAlpha
  · simpa only [U] using hQAlpha.2

end MetricCompactnessInputs
end HCGCompactness
end DifferentialGeometry
