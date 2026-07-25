import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepCStageSeed

set_option autoImplicit false









noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Filter Set Bundle Manifold
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Geometry.Riemannian

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}



structure NestedSubseq where
  sigma : Nat → Nat → Nat
  tau : Nat → Nat → Nat
  sigma_strict : ∀ m, StrictMono (sigma m)
  tau_strict : ∀ m, StrictMono (tau m)
  sigma_zero : sigma 0 = id
  sigma_succ : ∀ m, sigma (m + 1) = sigma m ∘ tau m

namespace NestedSubseq


def diag (T : NestedSubseq) (m : Nat) : Nat := T.sigma (m + 1) m


def tailComp (T : NestedSubseq) (q : Nat) : Nat → (Nat → Nat)
  | 0 => id
  | n + 1 => T.tailComp q n ∘ T.tau (q + 1 + n)



def tailFactor (T : NestedSubseq) (q n : Nat) : Nat :=
  T.tailComp q n (q + n)


theorem tailComp_strict (T : NestedSubseq) (q : Nat) :
    ∀ n, StrictMono (T.tailComp q n) := by
  intro n
  induction n with
  | zero => exact strictMono_id
  | succ n ih =>
      exact ih.comp (T.tau_strict (q + 1 + n))



theorem sigma_factor (T : NestedSubseq) (q n : Nat) :
    T.sigma (q + n + 1) = T.sigma (q + 1) ∘ T.tailComp q n := by
  induction n with
  | zero =>
      simp only [Nat.add_zero, tailComp, Function.comp_id]
  | succ n ih =>
      rw [show q + (n + 1) + 1 = (q + n + 1) + 1 by omega]
      rw [T.sigma_succ (q + n + 1), ih]
      ext x
      simp only [tailComp, Function.comp_apply]
      rw [show q + n + 1 = q + 1 + n by omega]


theorem tailFactor_strict (T : NestedSubseq) (q : Nat) :
    StrictMono (T.tailFactor q) := by
  apply strictMono_nat_of_lt_succ
  intro n
  dsimp only [tailFactor]
  rw [tailComp]
  simp only [Function.comp_apply]
  apply T.tailComp_strict q n
  have hlt : q + n < q + (n + 1) := by omega
  have hle := (T.tau_strict (q + 1 + n)).id_le (q + (n + 1))
  exact hlt.trans_le hle


theorem diag_strict (T : NestedSubseq) : StrictMono T.diag := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [diag, diag, T.sigma_succ (n + 1)]
  simp only [Function.comp_apply]
  apply T.sigma_strict (n + 1)
  have hle := (T.tau_strict (n + 1)).id_le (n + 1)
  exact (Nat.lt_succ_self n).trans_le hle



theorem diag_step_factor (T : NestedSubseq) (q n : Nat) :
    T.diag (q + n) =
      T.sigma q (T.tau q (T.tailFactor q n)) := by
  have hfactor := congrFun (T.sigma_factor q n) (q + n)
  rw [T.sigma_succ q] at hfactor
  simpa only [diag, tailFactor, Function.comp_apply] using hfactor

end NestedSubseq


structure StagePayload
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M)
    (r : Real) (hr : 0 ≤ r) where
  phi : Nat → Nat
  phi_strict : StrictMono phi
  U : LiveSlot L inp.pack r → Set E
  C0 : LiveSlot L inp.pack r → Set E
  C1 : LiveSlot L inp.pack r → Set E
  aInf : (alpha : LiveSlot L inp.pack r) →
    Fin (inp.pack.A r) → E → Real
  Jinf : (alpha : LiveSlot L inp.pack r) →
    InterSlot L inp.pack r alpha → E → E
  Jbarinf : (alpha : LiveSlot L inp.pack r) →
    InterSlot L inp.pack r alpha → E → E
  gInf : LiveSlot L inp.pack r →
    E → (E →L[Real] E →L[Real] Real)
  data : HasStageJetData inp P L hr phi phi_strict hconn U C0 C1
    aInf Jinf Jbarinf gInf


theorem HasStageRefine.payload_nonempty
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M)
    (r : Real) (hr : 0 ≤ r)
    (h : HasStageRefine inp P L hconn r hr) :
    Nonempty (StagePayload inp P L hconn r hr) := by
  rcases h with ⟨phi, hphi, U, C0, C1, aInf, Jinf, Jbarinf, gInf, hdata⟩
  exact ⟨⟨phi, hphi, U, C0, C1, aInf, Jinf, Jbarinf, gInf, hdata⟩⟩


structure StageState where
  sigma : Nat → Nat
  sigma_strict : StrictMono sigma



noncomputable def choosePayload
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L0 : NetLimitData inp.decay inp.D P)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M)
    (hseed : HasStageSeed inp P L0 hconn)
    (S : StageState) (m : Nat) :
    StagePayload inp P (L0.subseq S.sigma_strict) hconn (m : Real)
      (Nat.cast_nonneg m) :=
  Classical.choice <| HasStageRefine.payload_nonempty inp P
    (L0.subseq S.sigma_strict) hconn (m : Real) (Nat.cast_nonneg m) <|
      hseed.refine inp P L0 hconn (L0.subseq S.sigma_strict)
        (NetLimitData.stable_subseq inp.decay P L0 S.sigma_strict hseed.1)
        (m : Real) (Nat.cast_nonneg m)


noncomputable def nextState
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L0 : NetLimitData inp.decay inp.D P)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M)
    (hseed : HasStageSeed inp P L0 hconn)
    (S : StageState) (m : Nat) : StageState :=
  let d := choosePayload inp P L0 hconn hseed S m
  ⟨S.sigma ∘ d.phi, S.sigma_strict.comp d.phi_strict⟩


noncomputable def stageStates
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L0 : NetLimitData inp.decay inp.D P)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M)
    (hseed : HasStageSeed inp P L0 hconn) : Nat → StageState
  | 0 => ⟨id, strictMono_id⟩
  | m + 1 => nextState inp P L0 hconn hseed
      (stageStates inp P L0 hconn hseed m) m


noncomputable def radiusPayload
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L0 : NetLimitData inp.decay inp.D P)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M)
    (hseed : HasStageSeed inp P L0 hconn) (m : Nat) :=
  choosePayload inp P L0 hconn hseed
    (stageStates inp P L0 hconn hseed m) m


noncomputable def stageNested
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L0 : NetLimitData inp.decay inp.D P)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M)
    (hseed : HasStageSeed inp P L0 hconn) : NestedSubseq where
  sigma m := (stageStates inp P L0 hconn hseed m).sigma
  tau m := (radiusPayload inp P L0 hconn hseed m).phi
  sigma_strict m := (stageStates inp P L0 hconn hseed m).sigma_strict
  tau_strict m := (radiusPayload inp P L0 hconn hseed m).phi_strict
  sigma_zero := rfl
  sigma_succ m := by
    rw [stageStates]
    rfl



def HasRadiusTail
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L0 : NetLimitData inp.decay inp.D P)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M)
    (hseed : HasStageSeed inp P L0 hconn)
    (psi : Nat → Nat) (q : Nat) : Prop :=
  let S := stageStates inp P L0 hconn hseed q
  let d := radiusPayload inp P L0 hconn hseed q
  ∃ (rho : Nat → Nat) (hrho : StrictMono rho),
    (∀ n,
      (((L0.subseq S.sigma_strict).subseq
        (d.phi_strict.comp hrho)).φ n) = psi (q + n)) ∧
    HasStageJetData inp P (L0.subseq S.sigma_strict)
      (Nat.cast_nonneg q) (d.phi ∘ rho) (d.phi_strict.comp hrho)
      hconn d.U d.C0 d.C1 d.aInf d.Jinf d.Jbarinf d.gInf




theorem HasStageSeed.exists_radius_diag
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L0 : NetLimitData inp.decay inp.D P)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M)
    (hseed : HasStageSeed inp P L0 hconn) :
    ∃ (psi : Nat → Nat) (_hpsi : StrictMono psi),
      ∀ q : Nat, HasRadiusTail inp P L0 hconn hseed psi q := by
  let T := stageNested inp P L0 hconn hseed
  let psi := L0.φ ∘ T.diag
  have hpsi : StrictMono psi := L0.φ_mono.comp T.diag_strict
  refine ⟨psi, hpsi, ?_⟩
  intro q
  let S := stageStates inp P L0 hconn hseed q
  let d := radiusPayload inp P L0 hconn hseed q
  let rho := T.tailFactor q
  have hrho : StrictMono rho := T.tailFactor_strict q
  change ∃ (rho : Nat → Nat) (hrho : StrictMono rho),
    (∀ n,
      (((L0.subseq S.sigma_strict).subseq
        (d.phi_strict.comp hrho)).φ n) = psi (q + n)) ∧
    HasStageJetData inp P (L0.subseq S.sigma_strict)
      (Nat.cast_nonneg q) (d.phi ∘ rho) (d.phi_strict.comp hrho)
      hconn d.U d.C0 d.C1 d.aInf d.Jinf d.Jbarinf d.gInf
  refine ⟨rho, hrho, ?_, ?_⟩
  · intro n
    have hfactor := congrArg L0.φ (T.diag_step_factor q n)
    simpa only [NetLimitData.subseq_phi, Function.comp_apply, psi, T, S, d,
      rho, stageNested] using hfactor.symm
  · exact d.data.subseq inp P (L0.subseq S.sigma_strict)
      (Nat.cast_nonneg q) d.phi_strict hconn d.U d.C0 d.C1 d.aInf
      d.Jinf d.Jbarinf d.gInf hrho



theorem MetricCompactBase.exists_stage_diag
    (b : MetricCompactBase (I := I) X)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M) :
    ∃ (inp : MetricCompactnessInputs (I := I) X)
        (L0 : NetLimitData inp.decay inp.D
          (inp.properMetrics hcomplete hconn))
        (hseed : HasStageSeed inp (inp.properMetrics hcomplete hconn)
          L0 hconn)
        (psi : Nat → Nat) (_hpsi : StrictMono psi),
      ∀ q : Nat, HasRadiusTail inp (inp.properMetrics hcomplete hconn)
        L0 hconn hseed psi q := by
  obtain ⟨inp, L0, hseed⟩ := b.exists_stage_seed hcomplete hconn
  obtain ⟨psi, hpsi, htail⟩ :=
    hseed.exists_radius_diag inp (inp.properMetrics hcomplete hconn)
      L0 hconn
  exact ⟨inp, L0, hseed, psi, hpsi, htail⟩

end HCGCompactness
end DifferentialGeometry
