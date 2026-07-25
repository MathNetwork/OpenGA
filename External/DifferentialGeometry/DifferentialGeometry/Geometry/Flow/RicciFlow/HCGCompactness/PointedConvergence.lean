import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.Basic
import DifferentialGeometry.Geometry.Metric.OpenSubtype
import DifferentialGeometry.Geometry.Metric.Pullback
import DifferentialGeometry.Tensor.RSTensor.MetricCompatibility
import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.Regularity.TotalNabla0S
import DifferentialGeometry.Bundle.Frame
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.MFDeriv.Basic

set_option autoImplicit false
set_option linter.style.longLine false









noncomputable section

universe u

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}

section FixedManifoldMetricConvergence

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [T2Space M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M]




noncomputable def metricCovDerivStep
    (gRef : SmoothRiemannianMetric I M) (a : Nat)
    (A :
      Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (a + 2)) :
    Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (a + 3) := by
  haveI : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞)
      (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  haveI : IsManifold I 2 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞)
      (by decide : (2 : WithTop ℕ∞) ≤ ∞)
  haveI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
    change IsManifold I ∞ M
    infer_instance
  let cov :=
    DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) gRef
  let hcov :
      CovariantDerivative.ContMDiffCovariantDerivativeLocally
        (I := I) (E := E) (M := M) cov (∞ : WithTop ℕ∞) := by
    simpa [cov] using
      DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
        (I := I) (M := M) gRef
  let hreg :=
    Tensor0SBundle.totalNabla0S_reg (E := E) (H := H)
      (I := I) (M := M) (a + 2) cov hcov A
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, cov, hcov, hreg]
    using
      Tensor0SBundle.totalNabla0S (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (a + 2) cov A hreg




noncomputable def metricCovDeriv
    (h gRef : SmoothRiemannianMetric I M) :
    (a : Nat) ->
      Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (a + 2) :=
  Nat.rec
    (motive := fun a : Nat =>
      Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (a + 2))
    (by
      haveI : IsManifold I 1 M :=
        IsManifold.of_le (I := I) (M := M) (n := ∞)
          (by decide : (1 : WithTop ℕ∞) ≤ ∞)
      haveI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
        change IsManifold I ∞ M
        infer_instance
      exact Tensor0SBundle.metricTensorField (I := I) (M := M) h)
    (fun a A =>
      by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          metricCovDerivStep (I := I) gRef a A)




omit [SigmaCompactSpace M] in
theorem metricCovDeriv_one_apply_section
    (h gRef : SmoothRiemannianMetric I M)
    (X :
      ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M -> Type _))
    (x : M) (slots : Fin 2 -> TangentSpace I x) :
    metricCovDeriv (I := I) h gRef 1 x (Fin.cons (X x) slots) =
      Tensor0SBundle.nabla0SFun (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) 2
        (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) gRef)
        X (metricCovDeriv (I := I) h gRef 0) x slots := by
  haveI : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞)
      (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  haveI : IsManifold I 2 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞)
      (by decide : (2 : WithTop ℕ∞) ≤ ∞)
  haveI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
    change IsManifold I ∞ M
    infer_instance
  let cov :=
    DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) gRef
  let A : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2 :=
    metricCovDeriv (I := I) h gRef 0
  let hcov :
      CovariantDerivative.ContMDiffCovariantDerivativeLocally
        (I := I) (E := E) (M := M) cov (∞ : WithTop ℕ∞) := by
    simpa [cov] using
      DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
        (I := I) (M := M) gRef
  let hreg :=
    Tensor0SBundle.totalNabla0S_reg (E := E) (H := H)
      (I := I) (M := M) 2 cov hcov A
  change
    (Tensor0SBundle.totalNabla0S (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) 2 cov A hreg x) (Fin.cons (X x) slots) =
      Tensor0SBundle.nabla0SFun (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) 2 cov X A x slots
  exact Tensor0SBundle.totalNabla0SFun_apply_section
    (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 cov X A x slots




omit [SigmaCompactSpace M] in
theorem metricCovDeriv_one_eval_smooth_slots
    (h gRef : SmoothRiemannianMetric I M)
    (X :
      ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M -> Type _))
    (V : Fin 2 ->
      ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M -> Type _))
    (x : M) :
    metricCovDeriv (I := I) h gRef 1 x
        (Fin.cons (X x) (fun a : Fin 2 => V a x)) =
      extDerivFun (I := I)
          (fun p : M => h.inner p (V 0 p) (V 1 p)) x (X x) -
        ∑ a : Fin 2,
          h.inner x
            ((Function.update (fun b : Fin 2 => V b x) a
              (((DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) gRef)
                  (fun p : M => V a p) x) (X x))) 0)
            ((Function.update (fun b : Fin 2 => V b x) a
              (((DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) gRef)
                  (fun p : M => V a p) x) (X x))) 1) := by
  classical
  haveI : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞)
      (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  haveI : IsManifold I 2 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞)
      (by decide : (2 : WithTop ℕ∞) ≤ ∞)
  haveI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
    change IsManifold I ∞ M
    infer_instance
  let cov :=
    DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) gRef
  have hzero :
      metricCovDeriv (I := I) h gRef 0 =
        Tensor0SBundle.metricTensorField (I := I) h := by
    rfl
  have hdir :=
    metricCovDeriv_one_apply_section (I := I) h gRef X x
      (fun a : Fin 2 => V a x)
  have heval :=
    Tensor0SBundle.nabla0SFun_eval_smooth_slots (𝕜 := Real)
      (E := E) (H := H) (I := I) (M := M)
      cov X V (metricCovDeriv (I := I) h gRef 0) x
  rw [hdir, heval]
  simp [hzero, cov, Tensor0SBundle.metricTensorField_apply]

omit [FiniteDimensional ℝ E] [CompleteSpace E] [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M] in
private theorem extDerivFun_congr_eventually_real
    {f g : M -> Real} {x : M} (v : TangentSpace I x)
    (h : f =ᶠ[𝓝 x] g) :
    extDerivFun (I := I) f x v = extDerivFun (I := I) g x v := by
  have hmf := Filter.EventuallyEq.mfderiv_eq (I := I) (I' := 𝓘(Real, Real)) h
  have hx : f x = g x := h.eq_of_nhds
  unfold extDerivFun
  rw [hmf, hx]








omit [SigmaCompactSpace M] in
theorem metricCovDeriv_one_eval_localFrame
    {Idx : Type*} {u : Set M}
    (h gRef : SmoothRiemannianMetric I M)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u)
    (d a b : Idx) :
    metricCovDeriv (I := I) h gRef 1 x
        (Fin.cons (frame d x)
          (fun q : Fin 2 => if q = 0 then frame a x else frame b x)) =
      extDerivFun (I := I)
          (fun y : M => h.inner y (frame a y) (frame b y)) x (frame d x) -
        (h.inner x
            (((DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) gRef)
                (frame a) x) (frame d x))
            (frame b x) +
          h.inner x (frame a x)
            (((DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) gRef)
                (frame b) x) (frame d x))) := by
  classical
  haveI : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞)
      (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  haveI : IsManifold I 2 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞)
      (by decide : (2 : WithTop ℕ∞) ≤ ∞)
  haveI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
    change IsManifold I ∞ M
    infer_instance
  obtain ⟨sec, hsec⟩ :=
    hframe.exists_contMDiffSection_eqOn_nhd hu hx
  let cov :=
    DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) gRef
  let X :
      ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M -> Type _) := sec d
  let V : Fin 2 ->
      ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M -> Type _) :=
    fun q => if q = 0 then sec a else sec b
  have hsec_ev (i : Idx) :
      (fun y : M => sec i y) =ᶠ[𝓝 x] frame i :=
    hsec.mono fun y hy => hy i
  have hsec_x (i : Idx) : sec i x = frame i x :=
    (hsec_ev i).self_of_nhds
  have hpair_ev :
      (fun y : M => h.inner y (V 0 y) (V 1 y)) =ᶠ[𝓝 x]
        (fun y : M => h.inner y (frame a y) (frame b y)) := by
    filter_upwards [hsec_ev a, hsec_ev b] with y ha hb
    simp [V, ha, hb]
  have hXx : X x = frame d x := by
    simpa [X] using hsec_x d
  have hV0x : V 0 x = frame a x := by
    simp [V, hsec_x a]
  have hV1x : V 1 x = frame b x := by
    simp [V, hsec_x b]
  have hcov_a :
      ((cov (fun y : M => V 0 y) x) (X x)) =
        ((cov (frame a) x) (frame d x)) := by
    have hconn :
        cov (fun y : M => V 0 y) x = cov (frame a) x := by
      exact cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
        ((V 0).contMDiff.contMDiffAt.mdifferentiableAt (by simp))
        ((hframe.contMDiffAt hu hx a).mdifferentiableAt (by simp))
        (by simp)
        (by simpa [V] using hsec_ev a)
    rw [hconn, hXx]
  have hcov_b :
      ((cov (fun y : M => V 1 y) x) (X x)) =
        ((cov (frame b) x) (frame d x)) := by
    have hconn :
        cov (fun y : M => V 1 y) x = cov (frame b) x := by
      exact cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
        ((V 1).contMDiff.contMDiffAt.mdifferentiableAt (by simp))
        ((hframe.contMDiffAt hu hx b).mdifferentiableAt (by simp))
        (by simp)
        (by simpa [V] using hsec_ev b)
    rw [hconn, hXx]
  have hcov_a' :
      (((DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) gRef)
          (fun y : M => sec a y) x) (X x)) =
        (((DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) gRef)
          (frame a) x) (frame d x)) := by
    simpa [cov, V] using hcov_a
  have hcov_b' :
      (((DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) gRef)
          (fun y : M => sec b y) x) (X x)) =
        (((DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) gRef)
          (frame b) x) (frame d x)) := by
    simpa [cov, V] using hcov_b
  have hcov_a_candidate :
      ((DifferentialGeometry.Integral.Connection.leviCivitaConnectionCandidateAt (I := I) gRef
          (fun y : M => sec a y) x) (X x)) =
        ((DifferentialGeometry.Integral.Connection.leviCivitaConnectionCandidateAt (I := I) gRef
          (frame a) x) (frame d x)) := by
    simpa [DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric] using hcov_a'
  have hcov_b_candidate :
      ((DifferentialGeometry.Integral.Connection.leviCivitaConnectionCandidateAt (I := I) gRef
          (fun y : M => sec b y) x) (X x)) =
        ((DifferentialGeometry.Integral.Connection.leviCivitaConnectionCandidateAt (I := I) gRef
          (frame b) x) (frame d x)) := by
    simpa [DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric] using hcov_b'
  have hmain :=
    metricCovDeriv_one_eval_smooth_slots (I := I) h gRef X V x
  have hderiv :
      extDerivFun (I := I)
          (fun y : M => h.inner y (V 0 y) (V 1 y)) x (X x) =
        extDerivFun (I := I)
          (fun y : M => h.inner y (frame a y) (frame b y)) x
          (frame d x) := by
    rw [hXx]
    exact extDerivFun_congr_eventually_real (I := I) (x := x)
      (frame d x) hpair_ev
  calc
    metricCovDeriv (I := I) h gRef 1 x
        (Fin.cons (frame d x)
          (fun q : Fin 2 => if q = 0 then frame a x else frame b x))
        =
      metricCovDeriv (I := I) h gRef 1 x
        (Fin.cons (X x) (fun q : Fin 2 => V q x)) := by
          congr
          · exact hXx.symm
          · funext q
            fin_cases q
            · simpa [V] using hV0x.symm
            · simpa [V] using hV1x.symm
    _ =
      extDerivFun (I := I)
          (fun y : M => h.inner y (frame a y) (frame b y)) x (frame d x) -
        (h.inner x
            (((DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) gRef)
                (frame a) x) (frame d x))
            (frame b x) +
          h.inner x (frame a x)
            (((DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) gRef)
                (frame b) x) (frame d x))) := by
          rw [hmain, hderiv, Fin.sum_univ_two]
          simp [V, hsec_x a, hsec_x b, hcov_a_candidate, hcov_b_candidate]

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in

omit [SigmaCompactSpace M] in
theorem metricCovDeriv_one_component_localFrame
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {u : Set M}
    (h gRef : SmoothRiemannianMetric I M)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u)
    (d a b : Idx) :
    Tensor0SBundle.component0S (I := I) (hframe.toBasisAt hx)
        (metricCovDeriv (I := I) h gRef 1 x)
        (Fin.cons d (fun q : Fin 2 => if q = 0 then a else b) :
          Fin 3 -> Idx) =
      extDerivFun (I := I)
          (fun y : M => h.inner y (frame a y) (frame b y)) x (frame d x) -
        (h.inner x
            (((DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) gRef)
                (frame a) x) (frame d x))
            (frame b x) +
          h.inner x (frame a x)
            (((DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) gRef)
                (frame b) x) (frame d x))) := by
  rw [Tensor0SBundle.component0S_apply]
  simp only [IsLocalFrameOn.toBasisAt_coe]
  have hslots :
      (fun a_1 : Fin 3 =>
        frame
          ((Fin.cons d (fun q : Fin 2 => if q = 0 then a else b) :
            Fin 3 -> Idx) a_1) x) =
      Fin.cons (frame d x)
        (fun q : Fin 2 => if q = 0 then frame a x else frame b x) := by
    funext q
    fin_cases q <;> rfl
  exact
    (congrArg
        (fun slots : Fin 3 -> TangentSpace I x =>
          metricCovDeriv (I := I) h gRef 1 x slots) hslots).trans
      (metricCovDeriv_one_eval_localFrame (I := I) h gRef frame hframe hu hx
        d a b)



noncomputable def metricDiffCovDerivAt
    (a : Nat) (gk gInf gRef : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SBundle.Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (a + 2) x :=
  metricCovDeriv (I := I) gk gRef a x -
    metricCovDeriv (I := I) gInf gRef a x




noncomputable def metricDerivNorm
    (a : Nat) (gk gInf gRef : SmoothRiemannianMetric I M) (x : M) : Real :=
  Real.sqrt
    (Tensor0SBundle.normSq0S (I := I) gRef x (a + 2)
      (metricDiffCovDerivAt (I := I) a gk gInf gRef x))





noncomputable def metricDerivNormSupOn
    (K : Set M) (p : Nat)
    (gk gInf gRef : SmoothRiemannianMetric I M) : Real :=
  sSup {r : Real |
    exists a : Nat, a <= p ∧
      exists x : M, x ∈ K ∧
        metricDerivNorm (I := I) a gk gInf gRef x = r}





def MetricCPConvOn
    (K : Set M) (_hK : IsCompact K) (p : Nat)
    (gSeq : Nat -> SmoothRiemannianMetric I M)
    (gInf gRef : SmoothRiemannianMetric I M) : Prop :=
  forall ε : Real, 0 < ε ->
    exists k0 : Nat, forall k : Nat, k0 <= k ->
      metricDerivNormSupOn (I := I) K p (gSeq k) gInf gRef < ε



def MetricCInfConvOn
    (K : Set M) (hK : IsCompact K)
    (gSeq : Nat -> SmoothRiemannianMetric I M)
    (gInf gRef : SmoothRiemannianMetric I M) : Prop :=
  forall p : Nat, MetricCPConvOn (I := I) K hK p gSeq gInf gRef



def MetricCInfConvOnCompacts
    (gSeq : Nat -> SmoothRiemannianMetric I M)
    (gInf gRef : SmoothRiemannianMetric I M) : Prop :=
  forall K : Set M, forall hK : IsCompact K,
    MetricCInfConvOn (I := I) K hK gSeq gInf gRef



structure MetricCInfConvData
    (I : ModelWithCorners Real E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M]
    [T2Space M] [IsManifold I ∞ M]
    [SigmaCompactSpace M] where
  gSeq : Nat -> SmoothRiemannianMetric I M
  gInf : SmoothRiemannianMetric I M
  gRef : SmoothRiemannianMetric I M
  converges : MetricCInfConvOnCompacts (I := I) gSeq gInf gRef

end FixedManifoldMetricConvergence



structure ExhaustsByOpen {M : Type*} [TopologicalSpace M]
    (U : Nat -> Set M) : Prop where
  isOpen : forall k : Nat, IsOpen (U k)
  mono_step : forall k : Nat, U k ⊆ U (k + 1)
  subset :
    forall K : Set M, IsCompact K ->
      exists k0 : Nat, forall k : Nat, k0 <= k -> K ⊆ U k

namespace ExhaustsByOpen

theorem monotone {M : Type*} [TopologicalSpace M] {U : Nat -> Set M}
    (hU : ExhaustsByOpen U) :
    Monotone U := by
  intro i j hij
  induction hij with
  | refl => intro x hx; exact hx
  | step hle ih =>
      exact Set.Subset.trans ih (hU.mono_step _)

theorem subset_of_le {M : Type*} [TopologicalSpace M] {U : Nat -> Set M}
    (hU : ExhaustsByOpen U) {i j : Nat} (hij : i <= j) :
    U i ⊆ U j :=
  hU.monotone hij

end ExhaustsByOpen







structure PointedCGHMaps
    (X : PointedFlowSeq (I := I))
    (P : PointedRiemannianManifold (I := I))
    (subseq : Nat -> Nat) where
  partialDiffeomorph :
    forall k : Nat,
      letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : TopologicalSpace (X.term (subseq k)).M :=
        (X.term (subseq k)).topology
      letI : ChartedSpace H (X.term (subseq k)).M :=
        (X.term (subseq k)).charted
      PartialDiffeomorph I I P.M (X.term (subseq k)).M (∞ : WithTop ℕ∞)
  source_exhausts :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    ExhaustsByOpen (fun k =>
      letI : TopologicalSpace (X.term (subseq k)).M :=
        (X.term (subseq k)).topology
      letI : ChartedSpace H (X.term (subseq k)).M :=
        (X.term (subseq k)).charted
      (partialDiffeomorph k).source)
  base_mem :
    forall k : Nat,
      letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : TopologicalSpace (X.term (subseq k)).M :=
        (X.term (subseq k)).topology
      letI : ChartedSpace H (X.term (subseq k)).M :=
        (X.term (subseq k)).charted
      P.basepoint ∈ (partialDiffeomorph k).source
  basepoint_map :
    forall k : Nat,
      letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : TopologicalSpace (X.term (subseq k)).M :=
        (X.term (subseq k)).topology
      letI : ChartedSpace H (X.term (subseq k)).M :=
        (X.term (subseq k)).charted
      partialDiffeomorph k P.basepoint = (X.term (subseq k)).basepoint

namespace PointedCGHMaps

def source
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X P subseq) (k : Nat) : Set P.M := by
  letI : TopologicalSpace P.M := P.topology
  letI : ChartedSpace H P.M := P.charted
  letI : TopologicalSpace (X.term (subseq k)).M :=
    (X.term (subseq k)).topology
  letI : ChartedSpace H (X.term (subseq k)).M :=
    (X.term (subseq k)).charted
  exact (Φ.partialDiffeomorph k).source

def target
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X P subseq) (k : Nat) :
    Set ((X.term (subseq k)).M) := by
  letI : TopologicalSpace P.M := P.topology
  letI : ChartedSpace H P.M := P.charted
  letI : TopologicalSpace (X.term (subseq k)).M :=
    (X.term (subseq k)).topology
  letI : ChartedSpace H (X.term (subseq k)).M :=
    (X.term (subseq k)).charted
  exact (Φ.partialDiffeomorph k).target

def map
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X P subseq) (k : Nat) :
    P.M -> (X.term (subseq k)).M := by
  letI : TopologicalSpace P.M := P.topology
  letI : ChartedSpace H P.M := P.charted
  letI : TopologicalSpace (X.term (subseq k)).M :=
    (X.term (subseq k)).topology
  letI : ChartedSpace H (X.term (subseq k)).M :=
    (X.term (subseq k)).charted
  exact fun x => (Φ.partialDiffeomorph k) x

theorem source_open
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X P subseq) (k : Nat) :
    letI : TopologicalSpace P.M := P.topology
    IsOpen (Φ.source k) := by
  letI : TopologicalSpace P.M := P.topology
  letI : ChartedSpace H P.M := P.charted
  letI : TopologicalSpace (X.term (subseq k)).M :=
    (X.term (subseq k)).topology
  letI : ChartedSpace H (X.term (subseq k)).M :=
    (X.term (subseq k)).charted
  exact (Φ.partialDiffeomorph k).open_source

theorem target_open
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X P subseq) (k : Nat) :
    letI : TopologicalSpace (X.term (subseq k)).M :=
      (X.term (subseq k)).topology
    IsOpen (Φ.target k) := by
  letI : TopologicalSpace P.M := P.topology
  letI : ChartedSpace H P.M := P.charted
  letI : TopologicalSpace (X.term (subseq k)).M :=
    (X.term (subseq k)).topology
  letI : ChartedSpace H (X.term (subseq k)).M :=
    (X.term (subseq k)).charted
  exact (Φ.partialDiffeomorph k).open_target

theorem source_mono
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X P subseq) (k : Nat) :
    letI : TopologicalSpace P.M := P.topology
    Φ.source k ⊆ Φ.source (k + 1) := by
  letI : TopologicalSpace P.M := P.topology
  exact Φ.source_exhausts.mono_step k

theorem source_subset
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X P subseq)
    {K : Set P.M}
    (hK :
      letI : TopologicalSpace P.M := P.topology
      IsCompact K) :
    exists k0 : Nat, forall k : Nat, k0 <= k -> K ⊆ Φ.source k := by
  letI : TopologicalSpace P.M := P.topology
  exact Φ.source_exhausts.subset K hK

end PointedCGHMaps



def sourceOpen
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X P subseq) (k : Nat) :
    letI : TopologicalSpace P.M := P.topology
    TopologicalSpace.Opens P.M := by
  letI : TopologicalSpace P.M := P.topology
  exact ⟨Φ.source k, Φ.source_open k⟩



def targetOpen
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X P subseq) (k : Nat) :
    letI : TopologicalSpace (X.term (subseq k)).M :=
      (X.term (subseq k)).topology
    TopologicalSpace.Opens ((X.term (subseq k)).M) := by
  letI : TopologicalSpace (X.term (subseq k)).M :=
    (X.term (subseq k)).topology
  exact ⟨Φ.target k, Φ.target_open k⟩





abbrev SourceDomain
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X P subseq) (k : Nat) :=
  letI : TopologicalSpace P.M := P.topology
  (sourceOpen (I := I) Φ k : Type _)


abbrev TargetDomain
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X P subseq) (k : Nat) :=
  letI : TopologicalSpace (X.term (subseq k)).M :=
    (X.term (subseq k)).topology
  (targetOpen (I := I) Φ k : Type _)


@[implicit_reducible]
noncomputable def sourceDomTop
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X P subseq) (k : Nat) :
    TopologicalSpace (SourceDomain (I := I) Φ k) := by
  letI : TopologicalSpace P.M := P.topology
  change TopologicalSpace (sourceOpen (I := I) Φ k)
  infer_instance


@[implicit_reducible]
noncomputable def sourceDomCharted
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X P subseq) (k : Nat) :
    letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
    ChartedSpace H (SourceDomain (I := I) Φ k) := by
  letI : TopologicalSpace P.M := P.topology
  letI : ChartedSpace H P.M := P.charted
  letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
  change ChartedSpace H (sourceOpen (I := I) Φ k)
  exact TopologicalSpace.Opens.instChartedSpace (H := H) (M := P.M)
    (s := sourceOpen (I := I) Φ k)


@[implicit_reducible]
noncomputable def sourceDomT2
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X P subseq) (k : Nat) :
    letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
    T2Space (SourceDomain (I := I) Φ k) := by
  letI : TopologicalSpace P.M := P.topology
  letI : T2Space P.M := P.t2
  letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
  change T2Space {x : P.M // x ∈ Φ.source k}
  infer_instance


@[implicit_reducible]
noncomputable def sourceDomSmooth
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X P subseq) (k : Nat) :
    letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
    letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
    IsManifold I ∞ (SourceDomain (I := I) Φ k) := by
  letI : TopologicalSpace P.M := P.topology
  letI : ChartedSpace H P.M := P.charted
  letI : IsManifold I ∞ P.M := P.smooth
  letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
  letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
  change IsManifold I ∞ (sourceOpen (I := I) Φ k)
  exact { (sourceOpen (I := I) Φ k).instHasGroupoid (contDiffGroupoid ∞ I) with }




theorem sourceDomSigmaOf
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X P subseq) (k : Nat)
    (hσ : letI : TopologicalSpace P.M := P.topology; IsSigmaCompact (Φ.source k)) :
    letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
    SigmaCompactSpace (SourceDomain (I := I) Φ k) := by
  letI : TopologicalSpace P.M := P.topology
  letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
  change SigmaCompactSpace {x : P.M // x ∈ Φ.source k}
  exact isSigmaCompact_iff_sigmaCompactSpace.mp hσ


@[implicit_reducible]
noncomputable def targetDomTop
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X P subseq) (k : Nat) :
    TopologicalSpace (TargetDomain (I := I) Φ k) := by
  letI : TopologicalSpace (X.term (subseq k)).M :=
    (X.term (subseq k)).topology
  change TopologicalSpace (targetOpen (I := I) Φ k)
  infer_instance


@[implicit_reducible]
noncomputable def targetDomCharted
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X P subseq) (k : Nat) :
    letI : TopologicalSpace (TargetDomain (I := I) Φ k) := targetDomTop (I := I) Φ k
    ChartedSpace H (TargetDomain (I := I) Φ k) := by
  letI : TopologicalSpace (X.term (subseq k)).M :=
    (X.term (subseq k)).topology
  letI : ChartedSpace H (X.term (subseq k)).M :=
    (X.term (subseq k)).charted
  letI : TopologicalSpace (TargetDomain (I := I) Φ k) := targetDomTop (I := I) Φ k
  change ChartedSpace H (targetOpen (I := I) Φ k)
  exact TopologicalSpace.Opens.instChartedSpace (H := H)
    (M := (X.term (subseq k)).M) (s := targetOpen (I := I) Φ k)


@[implicit_reducible]
noncomputable def targetDomT2
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X P subseq) (k : Nat) :
    letI : TopologicalSpace (TargetDomain (I := I) Φ k) := targetDomTop (I := I) Φ k
    T2Space (TargetDomain (I := I) Φ k) := by
  letI : TopologicalSpace (X.term (subseq k)).M :=
    (X.term (subseq k)).topology
  letI : T2Space (X.term (subseq k)).M :=
    (X.term (subseq k)).t2
  letI : TopologicalSpace (TargetDomain (I := I) Φ k) := targetDomTop (I := I) Φ k
  change T2Space {x : (X.term (subseq k)).M // x ∈ Φ.target k}
  infer_instance


@[implicit_reducible]
noncomputable def targetDomSmooth
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X P subseq) (k : Nat) :
    letI : TopologicalSpace (TargetDomain (I := I) Φ k) := targetDomTop (I := I) Φ k
    letI : ChartedSpace H (TargetDomain (I := I) Φ k) := targetDomCharted (I := I) Φ k
    IsManifold I ∞ (TargetDomain (I := I) Φ k) := by
  letI : TopologicalSpace (X.term (subseq k)).M :=
    (X.term (subseq k)).topology
  letI : ChartedSpace H (X.term (subseq k)).M :=
    (X.term (subseq k)).charted
  letI : IsManifold I ∞ (X.term (subseq k)).M :=
    (X.term (subseq k)).smooth
  letI : TopologicalSpace (TargetDomain (I := I) Φ k) := targetDomTop (I := I) Φ k
  letI : ChartedSpace H (TargetDomain (I := I) Φ k) := targetDomCharted (I := I) Φ k
  change IsManifold I ∞ (targetOpen (I := I) Φ k)
  exact { (targetOpen (I := I) Φ k).instHasGroupoid (contDiffGroupoid ∞ I) with }



theorem targetDomSigmaOf
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X P subseq) (k : Nat)
    (hσ :
      letI : TopologicalSpace (X.term (subseq k)).M :=
        (X.term (subseq k)).topology
      IsSigmaCompact (Φ.target k)) :
    letI : TopologicalSpace (TargetDomain (I := I) Φ k) := targetDomTop (I := I) Φ k
    SigmaCompactSpace (TargetDomain (I := I) Φ k) := by
  letI : TopologicalSpace (X.term (subseq k)).M :=
    (X.term (subseq k)).topology
  letI : TopologicalSpace (TargetDomain (I := I) Φ k) := targetDomTop (I := I) Φ k
  change SigmaCompactSpace {x : (X.term (subseq k)).M // x ∈ Φ.target k}
  exact isSigmaCompact_iff_sigmaCompactSpace.mp hσ

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
private theorem contMDiff_openCod
    {M N : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [TopologicalSpace N] [ChartedSpace H N]
    [IsManifold I ∞ M] [IsManifold I ∞ N]
    {U : TopologicalSpace.Opens N}
    {f : M -> U}
    (hf : ContMDiff I I (∞ : WithTop ℕ∞) (fun x : M => (f x : N))) :
    ContMDiff I I (∞ : WithTop ℕ∞) f := by
  haveI : IsManifold I ∞ U :=
    { U.instHasGroupoid (contDiffGroupoid ∞ I) with }
  rw [contMDiff_iff_target] at hf ⊢
  constructor
  · exact Continuous.subtype_mk hf.1 (fun x => (f x).2)
  · intro y
    have hy := hf.2 (y : N)
    simpa [Function.comp_def, extChartAt, TopologicalSpace.Opens.chartAt_eq] using hy



noncomputable def sourceTargetDiff
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X P subseq) (k : Nat) :
    letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
    letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
    letI : TopologicalSpace (TargetDomain (I := I) Φ k) := targetDomTop (I := I) Φ k
    letI : ChartedSpace H (TargetDomain (I := I) Φ k) := targetDomCharted (I := I) Φ k
    Diffeomorph I I (SourceDomain (I := I) Φ k) (TargetDomain (I := I) Φ k)
      (∞ : WithTop ℕ∞) := by
  letI : TopologicalSpace P.M := P.topology
  letI : ChartedSpace H P.M := P.charted
  letI : IsManifold I ∞ P.M := P.smooth
  letI : TopologicalSpace (X.term (subseq k)).M :=
    (X.term (subseq k)).topology
  letI : ChartedSpace H (X.term (subseq k)).M :=
    (X.term (subseq k)).charted
  letI : IsManifold I ∞ (X.term (subseq k)).M :=
    (X.term (subseq k)).smooth
  letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
  letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
  letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
  letI : TopologicalSpace (TargetDomain (I := I) Φ k) := targetDomTop (I := I) Φ k
  letI : ChartedSpace H (TargetDomain (I := I) Φ k) := targetDomCharted (I := I) Φ k
  letI : IsManifold I ∞ (TargetDomain (I := I) Φ k) := targetDomSmooth (I := I) Φ k
  let e := Φ.partialDiffeomorph k
  refine
    { toEquiv := e.toPartialEquiv.toEquiv
      contMDiff_toFun := ?_
      contMDiff_invFun := ?_ }
  · have hbase :
        ContMDiff I I (∞ : WithTop ℕ∞)
          (fun x : SourceDomain (I := I) Φ k => e (x : P.M)) := by
      intro x
      have hx : (x : P.M) ∈ e.source := x.2
      have hAt :
          ContMDiffAt I I (∞ : WithTop ℕ∞) (fun y : P.M => e y) (x : P.M) :=
        e.contMDiffOn_toFun.contMDiffAt (e.open_source.mem_nhds hx)
      exact (contMDiffAt_subtype_iff
        (U := sourceOpen (I := I) Φ k)
        (f := fun y : P.M => e y) (x := x)).2 hAt
    exact contMDiff_openCod (I := I) (U := targetOpen (I := I) Φ k) hbase
  · have hbase :
        ContMDiff I I (∞ : WithTop ℕ∞)
          (fun y : TargetDomain (I := I) Φ k => e.toPartialEquiv.symm (y : (X.term (subseq k)).M)) := by
      intro y
      have hy : (y : (X.term (subseq k)).M) ∈ e.target := y.2
      have hAt :
          ContMDiffAt I I (∞ : WithTop ℕ∞)
            (fun z : (X.term (subseq k)).M => e.toPartialEquiv.symm z)
            (y : (X.term (subseq k)).M) :=
        e.contMDiffOn_invFun.contMDiffAt (e.open_target.mem_nhds hy)
      exact (contMDiffAt_subtype_iff
        (U := targetOpen (I := I) Φ k)
            (f := fun z : (X.term (subseq k)).M => e.toPartialEquiv.symm z) (x := y)).2 hAt
    exact contMDiff_openCod (I := I) (U := sourceOpen (I := I) Φ k) hbase

@[simp]
theorem sourceTargetDiff_apply
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X P subseq) (k : Nat)
    (x : SourceDomain (I := I) Φ k) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : TopologicalSpace (X.term (subseq k)).M := (X.term (subseq k)).topology
    letI : ChartedSpace H (X.term (subseq k)).M := (X.term (subseq k)).charted
    letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
    letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
    letI : TopologicalSpace (TargetDomain (I := I) Φ k) := targetDomTop (I := I) Φ k
    letI : ChartedSpace H (TargetDomain (I := I) Φ k) := targetDomCharted (I := I) Φ k
    (sourceTargetDiff (I := I) Φ k x : (X.term (subseq k)).M) = Φ.map k (x : P.M) := by
  rfl

@[simp]
theorem sourceTargetDiff_symm_apply
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X P subseq) (k : Nat)
    (y : TargetDomain (I := I) Φ k) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : TopologicalSpace (X.term (subseq k)).M := (X.term (subseq k)).topology
    letI : ChartedSpace H (X.term (subseq k)).M := (X.term (subseq k)).charted
    letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
    letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
    letI : TopologicalSpace (TargetDomain (I := I) Φ k) := targetDomTop (I := I) Φ k
    letI : ChartedSpace H (TargetDomain (I := I) Φ k) := targetDomCharted (I := I) Φ k
    ((sourceTargetDiff (I := I) Φ k).symm y : P.M) =
      (Φ.partialDiffeomorph k).toPartialEquiv.symm (y : (X.term (subseq k)).M) := by
  rfl

def sourceCompactSet
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X P subseq) (k : Nat)
    (K : Set P.M) : Set (SourceDomain (I := I) Φ k) :=
  {x | (x : P.M) ∈ K}



def targetCompactSet
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X P subseq) (k : Nat)
    (K : Set (X.term (subseq k)).M) : Set (TargetDomain (I := I) Φ k) :=
  {x | (x : (X.term (subseq k)).M) ∈ K}




theorem sourceCompactSet_isCompact
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X P subseq) (k : Nat)
    {K : Set P.M}
    (hK : letI : TopologicalSpace P.M := P.topology; IsCompact K)
    (hKsrc : letI : TopologicalSpace P.M := P.topology; K ⊆ Φ.source k) :
    letI : TopologicalSpace P.M := P.topology
    IsCompact (sourceCompactSet (I := I) Φ k K) := by
  letI : TopologicalSpace P.M := P.topology
  change IsCompact ((Subtype.val : SourceDomain (I := I) Φ k -> P.M) ⁻¹' K)
  rw [Subtype.isCompact_iff]
  have hImage :
      Subtype.val '' ((Subtype.val : SourceDomain (I := I) Φ k -> P.M) ⁻¹' K) = K := by
    ext x
    constructor
    · rintro ⟨y, hyK, rfl⟩
      exact hyK
    · intro hxK
      exact ⟨⟨x, hKsrc hxK⟩, hxK, rfl⟩
  rw [hImage]
  exact hK



theorem targetCompactSet_isCompact
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X P subseq) (k : Nat)
    {K : Set (X.term (subseq k)).M}
    (hK :
      letI : TopologicalSpace (X.term (subseq k)).M :=
        (X.term (subseq k)).topology
      IsCompact K)
    (hKtgt :
      letI : TopologicalSpace (X.term (subseq k)).M :=
        (X.term (subseq k)).topology
      K ⊆ Φ.target k) :
    letI : TopologicalSpace (X.term (subseq k)).M :=
      (X.term (subseq k)).topology
    IsCompact (targetCompactSet (I := I) Φ k K) := by
  letI : TopologicalSpace (X.term (subseq k)).M :=
    (X.term (subseq k)).topology
  change IsCompact ((Subtype.val : TargetDomain (I := I) Φ k ->
      (X.term (subseq k)).M) ⁻¹' K)
  rw [Subtype.isCompact_iff]
  have hImage :
      Subtype.val '' ((Subtype.val : TargetDomain (I := I) Φ k ->
        (X.term (subseq k)).M) ⁻¹' K) = K := by
    ext x
    constructor
    · rintro ⟨y, hyK, rfl⟩
      exact hyK
    · intro hxK
      exact ⟨⟨x, hKtgt hxK⟩, hxK, rfl⟩
  rw [hImage]
  exact hK




structure SourceDomainMetricData
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X P subseq) (k : Nat) where
  topology : TopologicalSpace (SourceDomain (I := I) Φ k)
  charted : ChartedSpace H (SourceDomain (I := I) Φ k)
  t2 : T2Space (SourceDomain (I := I) Φ k)
  smooth : IsManifold I ∞ (SourceDomain (I := I) Φ k)
  sigmaCompact : SigmaCompactSpace (SourceDomain (I := I) Φ k)
  limitMetric :
    letI : TopologicalSpace (SourceDomain (I := I) Φ k) := topology
    letI : ChartedSpace H (SourceDomain (I := I) Φ k) := charted
    Real -> SmoothRiemannianMetric I (SourceDomain (I := I) Φ k)
  pullbackMetric :
    letI : TopologicalSpace (SourceDomain (I := I) Φ k) := topology
    letI : ChartedSpace H (SourceDomain (I := I) Φ k) := charted
    Real -> SmoothRiemannianMetric I (SourceDomain (I := I) Φ k)
  referenceMetric :
    letI : TopologicalSpace (SourceDomain (I := I) Φ k) := topology
    letI : ChartedSpace H (SourceDomain (I := I) Φ k) := charted
    Real -> SmoothRiemannianMetric I (SourceDomain (I := I) Φ k)
  limitMetricFamily :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : IsManifold I ∞ P.M := P.smooth
    Real -> SmoothRiemannianMetric I P.M
  compact_preimage :
    letI : TopologicalSpace (SourceDomain (I := I) Φ k) := topology
    letI : TopologicalSpace P.M := P.topology
    forall K : Set P.M, IsCompact K ->
      K ⊆ Φ.source k ->
      IsCompact (sourceCompactSet (I := I) Φ k K)
  limit_inner :
    letI : TopologicalSpace (SourceDomain (I := I) Φ k) := topology
    letI : ChartedSpace H (SourceDomain (I := I) Φ k) := charted
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : T2Space P.M := P.t2
    letI : IsManifold I ∞ P.M := P.smooth
    letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) P.M := by
      change IsManifold I ∞ P.M
      infer_instance
    letI : SigmaCompactSpace P.M := P.sigmaCompact
    forall (t : Real) (x : SourceDomain (I := I) Φ k)
      (v w : TangentSpace I x),
        (limitMetric t).inner x v w =
          (limitMetricFamily t).inner (x : P.M)
            ((mfderiv I I (fun y : SourceDomain (I := I) Φ k => (y : P.M)) x) v)
            ((mfderiv I I (fun y : SourceDomain (I := I) Φ k => (y : P.M)) x) w)
  pullback_inner :
    letI : TopologicalSpace (SourceDomain (I := I) Φ k) := topology
    letI : ChartedSpace H (SourceDomain (I := I) Φ k) := charted
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : T2Space P.M := P.t2
    letI : IsManifold I ∞ P.M := P.smooth
    letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) P.M := by
      change IsManifold I ∞ P.M
      infer_instance
    letI : SigmaCompactSpace P.M := P.sigmaCompact
    letI : TopologicalSpace (X.term (subseq k)).M :=
      (X.term (subseq k)).topology
    letI : ChartedSpace H (X.term (subseq k)).M :=
      (X.term (subseq k)).charted
    letI : T2Space (X.term (subseq k)).M :=
      (X.term (subseq k)).t2
    letI : IsManifold I ∞ (X.term (subseq k)).M :=
      (X.term (subseq k)).smooth
    letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) (X.term (subseq k)).M :=
      by
        change IsManifold I ∞ (X.term (subseq k)).M
        infer_instance
    letI : SigmaCompactSpace (X.term (subseq k)).M :=
      (X.term (subseq k)).sigmaCompact
    forall (t : Real) (x : SourceDomain (I := I) Φ k)
      (v w : TangentSpace I x),
        (pullbackMetric t).inner x v w =
          ((X.term (subseq k)).S.family.metric t).inner
            (Φ.map k (x : P.M))
            ((mfderiv I I
              (fun y : SourceDomain (I := I) Φ k => Φ.map k (y : P.M)) x) v)
            ((mfderiv I I
              (fun y : SourceDomain (I := I) Φ k => Φ.map k (y : P.M)) x) w)

namespace SourceDomainMetricData




noncomputable def ofCanonical
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat}
    {Φ : PointedCGHMaps (I := I) X P subseq}
    {k : Nat}
    (sigmaCompact :
      letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
      SigmaCompactSpace (SourceDomain (I := I) Φ k))
    (limitMetric :
      letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
      letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
      letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
      Real -> SmoothRiemannianMetric I (SourceDomain (I := I) Φ k))
    (pullbackMetric :
      letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
      letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
      letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
      Real -> SmoothRiemannianMetric I (SourceDomain (I := I) Φ k))
    (referenceMetric :
      letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
      letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
      letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
      Real -> SmoothRiemannianMetric I (SourceDomain (I := I) Φ k))
    (limitMetricFamily :
      letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      Real -> SmoothRiemannianMetric I P.M)
    (limit_inner :
      letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
      letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
      letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
      letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : T2Space P.M := P.t2
      letI : IsManifold I ∞ P.M := P.smooth
      letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) P.M := by
        change IsManifold I ∞ P.M
        infer_instance
      letI : SigmaCompactSpace P.M := P.sigmaCompact
      forall (t : Real) (x : SourceDomain (I := I) Φ k)
        (v w : TangentSpace I x),
          (limitMetric t).inner x v w =
            (limitMetricFamily t).inner (x : P.M)
              ((mfderiv I I (fun y : SourceDomain (I := I) Φ k => (y : P.M)) x) v)
              ((mfderiv I I (fun y : SourceDomain (I := I) Φ k => (y : P.M)) x) w))
    (pullback_inner :
      letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
      letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
      letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
      letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : T2Space P.M := P.t2
      letI : IsManifold I ∞ P.M := P.smooth
      letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) P.M := by
        change IsManifold I ∞ P.M
        infer_instance
      letI : SigmaCompactSpace P.M := P.sigmaCompact
      letI : TopologicalSpace (X.term (subseq k)).M :=
        (X.term (subseq k)).topology
      letI : ChartedSpace H (X.term (subseq k)).M :=
        (X.term (subseq k)).charted
      letI : T2Space (X.term (subseq k)).M :=
        (X.term (subseq k)).t2
      letI : IsManifold I ∞ (X.term (subseq k)).M :=
        (X.term (subseq k)).smooth
      letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) (X.term (subseq k)).M :=
        by
          change IsManifold I ∞ (X.term (subseq k)).M
          infer_instance
      letI : SigmaCompactSpace (X.term (subseq k)).M :=
        (X.term (subseq k)).sigmaCompact
      forall (t : Real) (x : SourceDomain (I := I) Φ k)
        (v w : TangentSpace I x),
          (pullbackMetric t).inner x v w =
            ((X.term (subseq k)).S.family.metric t).inner
              (Φ.map k (x : P.M))
              ((mfderiv I I
                (fun y : SourceDomain (I := I) Φ k => Φ.map k (y : P.M)) x) v)
              ((mfderiv I I
                (fun y : SourceDomain (I := I) Φ k => Φ.map k (y : P.M)) x) w)) :
    SourceDomainMetricData (I := I) Φ k where
  topology := sourceDomTop (I := I) Φ k
  charted := sourceDomCharted (I := I) Φ k
  t2 := sourceDomT2 (I := I) Φ k
  smooth := sourceDomSmooth (I := I) Φ k
  sigmaCompact := sigmaCompact
  limitMetric := limitMetric
  pullbackMetric := pullbackMetric
  referenceMetric := referenceMetric
  limitMetricFamily := limitMetricFamily
  compact_preimage := by
    intro K hK hKsrc
    exact sourceCompactSet_isCompact (I := I) Φ k hK hKsrc
  limit_inner := limit_inner
  pullback_inner := pullback_inner






noncomputable def ofRestrictPullback
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat}
    {Φ : PointedCGHMaps (I := I) X P subseq}
    {k : Nat}
    (hσsrc : letI : TopologicalSpace P.M := P.topology; IsSigmaCompact (Φ.source k))
    (hσtgt :
      letI : TopologicalSpace (X.term (subseq k)).M :=
        (X.term (subseq k)).topology
      IsSigmaCompact (Φ.target k))
    (referenceMetric :
      letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
      letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
      letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
      Real -> SmoothRiemannianMetric I (SourceDomain (I := I) Φ k))
    (limitMetricFamily :
      letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      Real -> SmoothRiemannianMetric I P.M) :
    SourceDomainMetricData (I := I) Φ k := by
  letI : TopologicalSpace P.M := P.topology
  letI : ChartedSpace H P.M := P.charted
  letI : T2Space P.M := P.t2
  letI : IsManifold I ∞ P.M := P.smooth
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) P.M := by
    change IsManifold I ∞ P.M
    infer_instance
  letI : SigmaCompactSpace P.M := P.sigmaCompact
  letI : TopologicalSpace (X.term (subseq k)).M :=
    (X.term (subseq k)).topology
  letI : ChartedSpace H (X.term (subseq k)).M :=
    (X.term (subseq k)).charted
  letI : T2Space (X.term (subseq k)).M := (X.term (subseq k)).t2
  letI : IsManifold I ∞ (X.term (subseq k)).M :=
    (X.term (subseq k)).smooth
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) (X.term (subseq k)).M := by
    change IsManifold I ∞ (X.term (subseq k)).M
    infer_instance
  letI : SigmaCompactSpace (X.term (subseq k)).M :=
    (X.term (subseq k)).sigmaCompact
  letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
  letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
  letI : T2Space (SourceDomain (I := I) Φ k) := sourceDomT2 (I := I) Φ k
  letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
  letI : SigmaCompactSpace (SourceDomain (I := I) Φ k) :=
    sourceDomSigmaOf (I := I) Φ k hσsrc
  letI : TopologicalSpace (TargetDomain (I := I) Φ k) := targetDomTop (I := I) Φ k
  letI : ChartedSpace H (TargetDomain (I := I) Φ k) := targetDomCharted (I := I) Φ k
  letI : T2Space (TargetDomain (I := I) Φ k) := targetDomT2 (I := I) Φ k
  letI : IsManifold I ∞ (TargetDomain (I := I) Φ k) := targetDomSmooth (I := I) Φ k
  letI : SigmaCompactSpace (TargetDomain (I := I) Φ k) :=
    targetDomSigmaOf (I := I) Φ k hσtgt
  refine SourceDomainMetricData.ofCanonical (I := I)
    (Φ := Φ) (k := k)
    (sourceDomSigmaOf (I := I) Φ k hσsrc)
    (fun t => by
      let sourceSigma : SigmaCompactSpace (sourceOpen (I := I) Φ k) := by
        change SigmaCompactSpace (SourceDomain (I := I) Φ k)
        exact sourceDomSigmaOf (I := I) Φ k hσsrc
      let sourceT2 : T2Space (sourceOpen (I := I) Φ k) := by
        change T2Space (SourceDomain (I := I) Φ k)
        exact sourceDomT2 (I := I) Φ k
      exact
        @SmoothRiemannianMetric.restrictOpen E inferInstance inferInstance H inferInstance I
          P.M P.topology P.charted P.smooth inferInstance
          (limitMetricFamily t) (sourceOpen (I := I) Φ k) sourceSigma sourceT2)
    (fun t => by
      let sourceSigma : SigmaCompactSpace (sourceOpen (I := I) Φ k) := by
        change SigmaCompactSpace (SourceDomain (I := I) Φ k)
        exact sourceDomSigmaOf (I := I) Φ k hσsrc
      let sourceT2 : T2Space (sourceOpen (I := I) Φ k) := by
        change T2Space (SourceDomain (I := I) Φ k)
        exact sourceDomT2 (I := I) Φ k
      let targetSigma : SigmaCompactSpace (targetOpen (I := I) Φ k) := by
        change SigmaCompactSpace (TargetDomain (I := I) Φ k)
        exact targetDomSigmaOf (I := I) Φ k hσtgt
      let targetT2 : T2Space (targetOpen (I := I) Φ k) := by
        change T2Space (TargetDomain (I := I) Φ k)
        exact targetDomT2 (I := I) Φ k
      let targetMetric : SmoothRiemannianMetric I (targetOpen (I := I) Φ k) :=
        @SmoothRiemannianMetric.restrictOpen E inferInstance inferInstance H inferInstance I
          (X.term (subseq k)).M (X.term (subseq k)).topology
          (X.term (subseq k)).charted (X.term (subseq k)).smooth inferInstance
          ((X.term (subseq k)).S.family.metric t) (targetOpen (I := I) Φ k)
          targetSigma targetT2
      exact
        @Diffeomorph.pullbackMetric E inferInstance inferInstance inferInstance H inferInstance I
          (SourceDomain (I := I) Φ k) (sourceDomTop (I := I) Φ k)
          (sourceDomCharted (I := I) Φ k) (sourceDomSmooth (I := I) Φ k)
          (TargetDomain (I := I) Φ k) (targetDomTop (I := I) Φ k)
          (targetDomCharted (I := I) Φ k) (targetDomSmooth (I := I) Φ k)
          sourceSigma sourceT2 targetMetric (sourceTargetDiff (I := I) Φ k))
    referenceMetric
    limitMetricFamily
    ?_ ?_
  · intro t x v w
    change (limitMetricFamily t).inner (x : P.M) v w =
      (limitMetricFamily t).inner (x : P.M)
        ((mfderiv I I (fun y : SourceDomain (I := I) Φ k => (y : P.M)) x) v)
        ((mfderiv I I (fun y : SourceDomain (I := I) Φ k => (y : P.M)) x) w)
    have hvinc :
        (mfderiv I I (fun y : SourceDomain (I := I) Φ k => (y : P.M)) x) v = v := by
      simpa only using
        mfderiv_subtype_val_apply (I := I) (sourceOpen (I := I) Φ k) x v
    have hwinc :
        (mfderiv I I (fun y : SourceDomain (I := I) Φ k => (y : P.M)) x) w = w := by
      simpa only using
        mfderiv_subtype_val_apply (I := I) (sourceOpen (I := I) Φ k) x w
    rw [hvinc, hwinc]
  · intro t x v w
    rw [Diffeomorph.pullbackMetric_inner]
    change ((X.term (subseq k)).S.family.metric t).inner
        ((sourceTargetDiff (I := I) Φ k x : TargetDomain (I := I) Φ k) :
          (X.term (subseq k)).M)
        ((mfderiv I I (sourceTargetDiff (I := I) Φ k) x) v)
        ((mfderiv I I (sourceTargetDiff (I := I) Φ k) x) w) =
      ((X.term (subseq k)).S.family.metric t).inner
        (Φ.map k (x : P.M))
        ((mfderiv I I
          (fun y : SourceDomain (I := I) Φ k => Φ.map k (y : P.M)) x) v)
        ((mfderiv I I
          (fun y : SourceDomain (I := I) Φ k => Φ.map k (y : P.M)) x) w)
    have hchain :
        mfderiv I I
            (fun y : SourceDomain (I := I) Φ k =>
              ((sourceTargetDiff (I := I) Φ k y : TargetDomain (I := I) Φ k) :
                (X.term (subseq k)).M)) x =
          (mfderiv I I
              (fun y : TargetDomain (I := I) Φ k => (y : (X.term (subseq k)).M))
              (sourceTargetDiff (I := I) Φ k x)).comp
            (mfderiv I I (sourceTargetDiff (I := I) Φ k) x) := by
      have hval :
          MDifferentiableAt I I
            (fun y : TargetDomain (I := I) Φ k => (y : (X.term (subseq k)).M))
            (sourceTargetDiff (I := I) Φ k x) := by
        exact ContMDiffAt.mdifferentiableAt
          ((contMDiff_subtype_val (I := I) (n := (∞ : WithTop ℕ∞))
            (U := targetOpen (I := I) Φ k)).contMDiffAt)
          (by simp)
      have hdiff :
          MDifferentiableAt I I (sourceTargetDiff (I := I) Φ k)
            x :=
        (sourceTargetDiff (I := I) Φ k).contMDiff.contMDiffAt.mdifferentiableAt
          (by simp)
      simpa [Function.comp_def] using
        (mfderiv_comp (I := I) (I' := I) (I'' := I) x hval hdiff)
    have hv :
        mfderiv I I
            (fun y : SourceDomain (I := I) Φ k =>
              ((sourceTargetDiff (I := I) Φ k y : TargetDomain (I := I) Φ k) :
                (X.term (subseq k)).M)) x v =
          mfderiv I I (sourceTargetDiff (I := I) Φ k) x v := by
      rw [hchain, ContinuousLinearMap.comp_apply]
      have htarget :
          (mfderiv I I
              (fun y : TargetDomain (I := I) Φ k => (y : (X.term (subseq k)).M))
              (sourceTargetDiff (I := I) Φ k x))
            ((mfderiv I I (sourceTargetDiff (I := I) Φ k) x) v) =
            (mfderiv I I (sourceTargetDiff (I := I) Φ k) x) v := by
        simpa only using
          mfderiv_subtype_val_apply (I := I) (targetOpen (I := I) Φ k)
            (sourceTargetDiff (I := I) Φ k x)
            ((mfderiv I I (sourceTargetDiff (I := I) Φ k) x) v)
      exact htarget
    have hw :
        mfderiv I I
            (fun y : SourceDomain (I := I) Φ k =>
              ((sourceTargetDiff (I := I) Φ k y : TargetDomain (I := I) Φ k) :
                (X.term (subseq k)).M)) x w =
          mfderiv I I (sourceTargetDiff (I := I) Φ k) x w := by
      rw [hchain, ContinuousLinearMap.comp_apply]
      have htarget :
          (mfderiv I I
              (fun y : TargetDomain (I := I) Φ k => (y : (X.term (subseq k)).M))
              (sourceTargetDiff (I := I) Φ k x))
            ((mfderiv I I (sourceTargetDiff (I := I) Φ k) x) w) =
            (mfderiv I I (sourceTargetDiff (I := I) Φ k) x) w := by
        simpa only using
          mfderiv_subtype_val_apply (I := I) (targetOpen (I := I) Φ k)
            (sourceTargetDiff (I := I) Φ k x)
            ((mfderiv I I (sourceTargetDiff (I := I) Φ k) x) w)
      exact htarget
    have hxmap :
        ((sourceTargetDiff (I := I) Φ k x : TargetDomain (I := I) Φ k) :
          (X.term (subseq k)).M) = Φ.map k (x : P.M) :=
      sourceTargetDiff_apply (I := I) Φ k x
    have hfun :
        (fun y : SourceDomain (I := I) Φ k =>
          ((sourceTargetDiff (I := I) Φ k y : TargetDomain (I := I) Φ k) :
            (X.term (subseq k)).M)) =
          fun y : SourceDomain (I := I) Φ k => Φ.map k (y : P.M) := by
      funext y
      exact sourceTargetDiff_apply (I := I) Φ k y
    rw [hxmap, ← hv, ← hw, hfun]
    rfl

noncomputable def derivNormSupOn
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat}
    {k : Nat}
    {Φ : PointedCGHMaps (I := I) X P subseq}
    (D : SourceDomainMetricData (I := I) Φ k)
    (K : Set P.M) (p : Nat) (t : Real) : Real := by
  letI : TopologicalSpace (SourceDomain (I := I) Φ k) := D.topology
  letI : ChartedSpace H (SourceDomain (I := I) Φ k) := D.charted
  letI : T2Space (SourceDomain (I := I) Φ k) := D.t2
  letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) := D.smooth
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1)
      (SourceDomain (I := I) Φ k) := by
    change IsManifold I ∞ (SourceDomain (I := I) Φ k)
    infer_instance
  letI : SigmaCompactSpace (SourceDomain (I := I) Φ k) := D.sigmaCompact
  exact metricDerivNormSupOn (I := I)
    (sourceCompactSet (I := I) Φ k K) p
    (D.pullbackMetric t) (D.limitMetric t) (D.referenceMetric t)

end SourceDomainMetricData

def SourceMetricCPConvOn
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X P subseq)
    (D : forall k : Nat, SourceDomainMetricData (I := I) Φ k)
    (K : Set P.M)
    (_hK : letI : TopologicalSpace P.M := P.topology; IsCompact K)
    (p : Nat) (t : Real) : Prop :=
  forall ε : Real, 0 < ε ->
    exists k0 : Nat, forall k : Nat, k0 <= k ->
      K ⊆ Φ.source k /\
        (D k).derivNormSupOn (I := I) K p t < ε

def SourceMetricCPConvOnWindow
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X P subseq)
    (D : forall k : Nat, SourceDomainMetricData (I := I) Φ k)
    (K : Set P.M)
    (_hK : letI : TopologicalSpace P.M := P.topology; IsCompact K)
    (p : Nat)
    (a b : Real) : Prop :=
  forall ε : Real, 0 < ε ->
    exists k0 : Nat, forall k : Nat, k0 <= k ->
      K ⊆ Φ.source k /\
        forall t : Real, t ∈ Set.Icc a b ->
          (D k).derivNormSupOn (I := I) K p t < ε






theorem SourceMetricCPConvOnWindow.of_derivNormSupOn
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat}
    {Φ : PointedCGHMaps (I := I) X P subseq}
    {D : forall k : Nat, SourceDomainMetricData (I := I) Φ k}
    {K : Set P.M}
    (hK : letI : TopologicalSpace P.M := P.topology; IsCompact K)
    {p : Nat} {a b : Real}
    (hconv : forall ε : Real, 0 < ε ->
      exists k0 : Nat, forall k : Nat, k0 <= k ->
        forall t : Real, t ∈ Set.Icc a b ->
          (D k).derivNormSupOn (I := I) K p t < ε) :
    SourceMetricCPConvOnWindow (I := I) Φ D K hK p a b := by
  intro ε hε
  obtain ⟨kSrc, hSrc⟩ := Φ.source_subset hK
  obtain ⟨kConv, hConv⟩ := hconv ε hε
  refine ⟨max kSrc kConv, fun k hk => ?_⟩
  refine ⟨hSrc k (le_trans (Nat.le_max_left kSrc kConv) hk), ?_⟩
  exact hConv k (le_trans (Nat.le_max_right kSrc kConv) hk)





structure SourceMetricConvergenceData
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X P subseq) where
  domain : forall k : Nat, SourceDomainMetricData (I := I) Φ k
  converges :
    forall K : Set P.M,
      forall hK : letI : TopologicalSpace P.M := P.topology; IsCompact K,
      forall p : Nat,
      forall t : Real, t ∈ X.D.carrier ->
        SourceMetricCPConvOn (I := I) Φ domain K hK p t

namespace SourceMetricConvergenceData





noncomputable def of_derivNormSupOn
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat}
    {Φ : PointedCGHMaps (I := I) X P subseq}
    {D : forall k : Nat, SourceDomainMetricData (I := I) Φ k}
    (hconv : forall K : Set P.M,
      forall _hK : letI : TopologicalSpace P.M := P.topology; IsCompact K,
      forall p : Nat,
      forall t : Real, t ∈ X.D.carrier ->
        forall ε : Real, 0 < ε ->
          exists k0 : Nat, forall k : Nat, k0 <= k ->
            (D k).derivNormSupOn (I := I) K p t < ε) :
    SourceMetricConvergenceData (I := I) Φ where
  domain := D
  converges := by
    intro K hK p t ht ε hε
    obtain ⟨kSrc, hSrc⟩ := Φ.source_subset hK
    obtain ⟨kConv, hConv⟩ := hconv K hK p t ht ε hε
    refine ⟨max kSrc kConv, fun k hk => ?_⟩
    refine ⟨hSrc k (le_trans (Nat.le_max_left kSrc kConv) hk), ?_⟩
    exact hConv k (le_trans (Nat.le_max_right kSrc kConv) hk)



noncomputable def ofRestrictPullback
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat}
    {Φ : PointedCGHMaps (I := I) X P subseq}
    (hσsrc : forall k : Nat,
      letI : TopologicalSpace P.M := P.topology
      IsSigmaCompact (Φ.source k))
    (hσtgt : forall k : Nat,
      letI : TopologicalSpace (X.term (subseq k)).M :=
        (X.term (subseq k)).topology
      IsSigmaCompact (Φ.target k))
    (referenceMetric : forall k : Nat,
      letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
      letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
      letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
      Real -> SmoothRiemannianMetric I (SourceDomain (I := I) Φ k))
    (limitMetricFamily :
      letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      Real -> SmoothRiemannianMetric I P.M)
    (hconv : forall K : Set P.M,
      forall _hK : letI : TopologicalSpace P.M := P.topology; IsCompact K,
      forall p : Nat,
      forall t : Real, t ∈ X.D.carrier ->
        forall ε : Real, 0 < ε ->
          exists k0 : Nat, forall k : Nat, k0 <= k ->
            ((SourceDomainMetricData.ofRestrictPullback (I := I)
              (Φ := Φ) (k := k) (hσsrc k) (hσtgt k)
              (referenceMetric k) limitMetricFamily).derivNormSupOn (I := I) K p t) < ε) :
    SourceMetricConvergenceData (I := I) Φ :=
  SourceMetricConvergenceData.of_derivNormSupOn (I := I)
    (D := fun k => SourceDomainMetricData.ofRestrictPullback (I := I)
      (Φ := Φ) (k := k) (hσsrc k) (hσtgt k) (referenceMetric k) limitMetricFamily)
    hconv

end SourceMetricConvergenceData


structure SourceSpacetimeConvergenceData
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X P subseq)
    (D : forall k : Nat, SourceDomainMetricData (I := I) Φ k) where
  converges_on_windows :
    forall K : Set P.M,
      forall hK : letI : TopologicalSpace P.M := P.topology; IsCompact K,
      forall p : Nat,
      forall a b : Real, Set.Icc a b ⊆ X.D.carrier ->
        SourceMetricCPConvOnWindow (I := I) Φ D K hK p a b

namespace SourceSpacetimeConvergenceData



noncomputable def toSpatial
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat}
    {Φ : PointedCGHMaps (I := I) X P subseq}
    {D : forall k : Nat, SourceDomainMetricData (I := I) Φ k}
    (Hst : SourceSpacetimeConvergenceData (I := I) Φ D) :
    SourceMetricConvergenceData (I := I) Φ where
  domain := D
  converges := by
    intro K hK p t ht ε hε
    have hwin : Set.Icc t t ⊆ X.D.carrier := by
      intro s hs
      have hst : s = t := le_antisymm hs.2 hs.1
      simpa [hst] using ht
    obtain ⟨k0, hk0⟩ := Hst.converges_on_windows K hK p t t hwin ε hε
    refine ⟨k0, fun k hk => ?_⟩
    obtain ⟨hsrc, hbound⟩ := hk0 k hk
    exact ⟨hsrc, hbound t ⟨le_rfl, le_rfl⟩⟩






theorem of_derivNormSupOn
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat}
    {Φ : PointedCGHMaps (I := I) X P subseq}
    {D : forall k : Nat, SourceDomainMetricData (I := I) Φ k}
    (hconv : forall K : Set P.M,
      forall _hK : letI : TopologicalSpace P.M := P.topology; IsCompact K,
      forall p : Nat,
      forall a b : Real, Set.Icc a b ⊆ X.D.carrier ->
        forall ε : Real, 0 < ε ->
          exists k0 : Nat, forall k : Nat, k0 <= k ->
            forall t : Real, t ∈ Set.Icc a b ->
              (D k).derivNormSupOn (I := I) K p t < ε) :
    SourceSpacetimeConvergenceData (I := I) Φ D where
  converges_on_windows := by
    intro K hK p a b hwin
    exact SourceMetricCPConvOnWindow.of_derivNormSupOn (I := I) hK
      (hconv K hK p a b hwin)




theorem ofRestrictPullback
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat}
    {Φ : PointedCGHMaps (I := I) X P subseq}
    (hσsrc : forall k : Nat,
      letI : TopologicalSpace P.M := P.topology
      IsSigmaCompact (Φ.source k))
    (hσtgt : forall k : Nat,
      letI : TopologicalSpace (X.term (subseq k)).M :=
        (X.term (subseq k)).topology
      IsSigmaCompact (Φ.target k))
    (referenceMetric : forall k : Nat,
      letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
      letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
      letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
      Real -> SmoothRiemannianMetric I (SourceDomain (I := I) Φ k))
    (limitMetricFamily :
      letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      Real -> SmoothRiemannianMetric I P.M)
    (hconv : forall K : Set P.M,
      forall _hK : letI : TopologicalSpace P.M := P.topology; IsCompact K,
      forall p : Nat,
      forall a b : Real, Set.Icc a b ⊆ X.D.carrier ->
        forall ε : Real, 0 < ε ->
          exists k0 : Nat, forall k : Nat, k0 <= k ->
            forall t : Real, t ∈ Set.Icc a b ->
              ((SourceDomainMetricData.ofRestrictPullback (I := I)
                (Φ := Φ) (k := k) (hσsrc k) (hσtgt k)
                (referenceMetric k) limitMetricFamily).derivNormSupOn (I := I) K p t) < ε) :
    SourceSpacetimeConvergenceData (I := I) Φ
      (fun k => SourceDomainMetricData.ofRestrictPullback (I := I)
        (Φ := Φ) (k := k) (hσsrc k) (hσtgt k) (referenceMetric k) limitMetricFamily) :=
  SourceSpacetimeConvergenceData.of_derivNormSupOn (I := I) hconv

end SourceSpacetimeConvergenceData










def FunctionPullbackTendsto
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat}
    (Phi : PointedCGHMaps (I := I) X P subseq)
    (uSeq : forall k : Nat, Real -> (X.term (subseq k)).M -> Real)
    (uInf : Real -> P.M -> Real) : Prop :=
  ∀ t ∈ X.D.carrier, forall x : P.M,
    Filter.Tendsto (fun k : Nat => uSeq k t (Phi.map k x))
      Filter.atTop (nhds (uInf t x))








theorem FunctionPullbackTendsto.le_of_bound0
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat}
    {Phi : PointedCGHMaps (I := I) X P subseq}
    {uSeq : forall k : Nat, Real -> (X.term (subseq k)).M -> Real}
    {uInf : Real -> P.M -> Real}
    (hconv : FunctionPullbackTendsto (I := I) Phi uSeq uInf)
    (bound : Real -> P.M -> Nat -> Real)
    (hbound :
      forall t : Real, forall x : P.M,
        Filter.Tendsto (bound t x) Filter.atTop (nhds 0) /\
          (∀ᶠ k in Filter.atTop,
            uSeq k t (Phi.map k x) <= bound t x k)) :
    ∀ t ∈ X.D.carrier, forall x : P.M, forall η : Real, 0 < η ->
      uInf t x <= η := by
  intro t ht x η hη
  have hle0 : uInf t x <= 0 := by
    exact le_of_tendsto_of_tendsto (hconv t ht x) (hbound t x).1 (hbound t x).2
  exact le_trans hle0 (le_of_lt hη)



def ScalarPullbackTendsto
    {X : PointedFlowSeq (I := I)}
    {L : PointedFlowData (I := I) X.D}
    {subseq : Nat -> Nat}
    (Phi : PointedCGHMaps (I := I) X (L.atTime 0) subseq) : Prop :=
  FunctionPullbackTendsto (I := I) Phi
    (fun k t x =>
      letI : TopologicalSpace (X.term (subseq k)).M :=
        (X.term (subseq k)).topology
      letI : ChartedSpace H (X.term (subseq k)).M :=
        (X.term (subseq k)).charted
      letI : IsManifold I ∞ (X.term (subseq k)).M :=
        (X.term (subseq k)).smooth
      letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) (X.term (subseq k)).M :=
        by
          change IsManifold I ∞ (X.term (subseq k)).M
          infer_instance
      letI : SigmaCompactSpace (X.term (subseq k)).M :=
        (X.term (subseq k)).sigmaCompact
      letI : T2Space (X.term (subseq k)).M :=
        (X.term (subseq k)).t2
      (X.term (subseq k)).S.scalar t x)
    (fun t x =>
      letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      letI : IsManifold I ∞ L.M := L.smooth
      letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) L.M := by
        change IsManifold I ∞ L.M
        infer_instance
      letI : SigmaCompactSpace L.M := L.sigmaCompact
      letI : T2Space L.M := L.t2
      L.S.scalar t x)



structure PointedCGConverges
    (X : PointedFlowSeq (I := I))
    (L : PointedFlowData (I := I) X.D)
    (subseq : Nat -> Nat) where
  maps : PointedCGHMaps (I := I) X (L.atTime 0) subseq
  metrics : SourceMetricConvergenceData (I := I) maps



structure SmoothCGHConverges
    (X : PointedFlowSeq (I := I))
    (L : PointedFlowData (I := I) X.D)
    (subseq : Nat -> Nat) where
  spatial : PointedCGConverges (I := I) X L subseq
  scalar_converges : ScalarPullbackTendsto (I := I) spatial.maps
  spacetime :
    SourceSpacetimeConvergenceData (I := I) spatial.maps
      spatial.metrics.domain

namespace SmoothCGHConverges




noncomputable def ofSpacetime
    {X : PointedFlowSeq (I := I)}
    {L : PointedFlowData (I := I) X.D}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X (L.atTime 0) subseq)
    {D : forall k : Nat, SourceDomainMetricData (I := I) Φ k}
    (hscalar : ScalarPullbackTendsto (I := I) Φ)
    (Hst : SourceSpacetimeConvergenceData (I := I) Φ D) :
    SmoothCGHConverges (I := I) X L subseq where
  spatial := {
    maps := Φ
    metrics := Hst.toSpatial (I := I) }
  scalar_converges := hscalar
  spacetime := Hst




noncomputable def ofRestrictPullback
    {X : PointedFlowSeq (I := I)}
    {L : PointedFlowData (I := I) X.D}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X (L.atTime 0) subseq)
    (hscalar : ScalarPullbackTendsto (I := I) Φ)
    (hσsrc : forall k : Nat,
      letI : TopologicalSpace (L.atTime 0).M := L.topology
      IsSigmaCompact (Φ.source k))
    (hσtgt : forall k : Nat,
      letI : TopologicalSpace (X.term (subseq k)).M :=
        (X.term (subseq k)).topology
      IsSigmaCompact (Φ.target k))
    (referenceMetric : forall k : Nat,
      letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
      letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
      letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
      Real -> SmoothRiemannianMetric I (SourceDomain (I := I) Φ k))
    (limitMetricFamily :
      letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      letI : IsManifold I ∞ L.M := L.smooth
      Real -> SmoothRiemannianMetric I L.M)
    (hconv : forall K : Set (L.atTime 0).M,
      forall _hK : letI : TopologicalSpace (L.atTime 0).M := L.topology; IsCompact K,
      forall p : Nat,
      forall a b : Real, Set.Icc a b ⊆ X.D.carrier ->
        forall ε : Real, 0 < ε ->
          exists k0 : Nat, forall k : Nat, k0 <= k ->
            forall t : Real, t ∈ Set.Icc a b ->
              ((SourceDomainMetricData.ofRestrictPullback (I := I)
                (Φ := Φ) (k := k) (hσsrc k) (hσtgt k)
                (referenceMetric k) limitMetricFamily).derivNormSupOn (I := I) K p t) < ε) :
    SmoothCGHConverges (I := I) X L subseq :=
  SmoothCGHConverges.ofSpacetime (I := I) Φ hscalar
    (SourceSpacetimeConvergenceData.ofRestrictPullback (I := I)
      hσsrc hσtgt referenceMetric limitMetricFamily hconv)

end SmoothCGHConverges

end HCGCompactness
end DifferentialGeometry
