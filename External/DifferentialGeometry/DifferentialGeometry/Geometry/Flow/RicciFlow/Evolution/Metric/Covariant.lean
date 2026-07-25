import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Metric.InverseSmooth

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedFintypeInType false










noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open DifferentialGeometry.Tensor.Coordinates
open scoped Manifold ContDiff BigOperators Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]

section Components

variable {Idx : Type*} [Fintype Idx]
variable {u : Set M}





def inverseMetricCovDerivCompInFrame
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (t : Real) (x : M) (d k l : Idx) : Real :=
  extDerivFun (I := I) (fun y : M => gInv t y k l) x (frame d x) +
    (∑ a : Idx,
      christoffelSymbolInFrame cov frame hframe x d a k * gInv t x a l) +
    (∑ a : Idx,
      christoffelSymbolInFrame cov frame hframe x d a l * gInv t x k a)

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [Fintype Idx] in
private theorem metric_localFrame_mdiffAt
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u) (i : Idx) :
    MDiffAt (T% (frame i)) x :=
  (hframe.contMDiffAt hu hx i).mdifferentiableAt one_ne_zero

omit [SigmaCompactSpace M] [T2Space M] in
theorem metricCompInFrame_extDerivFun_eq_christoffel
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (t : Real)
    (g : SmoothRiemannianMetric I M)
    (hmc : DifferentialGeometry.Integral.Connection.IsMetricCompatible_gen (I := I) cov g)
    (hg : g = S.family.metric t)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u)
    (d a b : Idx) :
    extDerivFun (I := I)
        (fun y : M => metricCompInFrame (I := I) S frame t y a b)
        x (frame d x) =
      (∑ p : Idx,
        christoffelSymbolInFrame cov frame hframe x d a p *
          metricCompInFrame (I := I) S frame t x p b) +
      (∑ p : Idx,
        christoffelSymbolInFrame cov frame hframe x d b p *
          metricCompInFrame (I := I) S frame t x a p) := by
  classical
  subst hg
  have hd := metric_localFrame_mdiffAt (I := I) frame hframe hu hx d
  have ha := metric_localFrame_mdiffAt (I := I) frame hframe hu hx a
  have hb := metric_localFrame_mdiffAt (I := I) frame hframe hu hx b
  have hmetric :=
    DifferentialGeometry.Integral.Connection.metric_compatible_apply
      (I := I) hmc (frame d) (frame a) (frame b) hd ha hb
  have hmetric' :
      extDerivFun (I := I)
          (fun y : M => metricCompInFrame (I := I) S frame t y a b)
          x (frame d x) =
        (S.family.metric t).inner x
          ((cov (frame a) x) (frame d x)) (frame b x) +
        (S.family.metric t).inner x (frame a x)
          ((cov (frame b) x) (frame d x)) := by
    simpa [extDerivFun, metricCompInFrame] using hmetric
  rw [hmetric']
  rw [covariantDerivative_eq_sum_christoffel (I := I) cov frame hframe hx d a]
  rw [covariantDerivative_eq_sum_christoffel (I := I) cov frame hframe hx d b]
  simp [metricCompInFrame, map_sum]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [IsManifold I 1 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem metric_mdiffAt_finset_sum
    {ι : Type*} (t : Finset ι) (f : ι -> M -> Real) {x : M}
    (hf : ∀ i ∈ t, MDifferentiableAt I 𝓘(Real, Real) (f i) x) :
    MDifferentiableAt I 𝓘(Real, Real) (t.sum f) x := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      simpa using (mdifferentiableAt_const
        (I := I) (I' := 𝓘(Real, Real)) (c := (0 : Real)) (x := x))
  | insert i t hit ih =>
      have hfi : MDifferentiableAt I 𝓘(Real, Real) (f i) x := hf i (by simp [hit])
      have hft : ∀ j ∈ t, MDifferentiableAt I 𝓘(Real, Real) (f j) x := by
        intro j hj
        exact hf j (by simp [hj])
      have hsum : MDifferentiableAt I 𝓘(Real, Real) (t.sum f) x := ih hft
      have hadd : MDifferentiableAt I 𝓘(Real, Real) (f i + t.sum f) x := hfi.add hsum
      simpa [Finset.sum_insert, hit] using hadd

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [IsManifold I 1 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem metric_extDerivFun_finset_sum
    {ι : Type*} (t : Finset ι) (f : ι -> M -> Real)
    {x : M} (v : TangentSpace I x)
    (hf : ∀ i ∈ t, MDifferentiableAt I 𝓘(Real, Real) (f i) x) :
    extDerivFun (I := I) (t.sum f) x v =
      t.sum (fun i => extDerivFun (I := I) (f i) x v) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      simp
  | insert i t hit ih =>
      have hfi : MDifferentiableAt I 𝓘(Real, Real) (f i) x := hf i (by simp [hit])
      have hft : ∀ j ∈ t, MDifferentiableAt I 𝓘(Real, Real) (f j) x := by
        intro j hj
        exact hf j (by simp [hj])
      have hsum : MDifferentiableAt I 𝓘(Real, Real) (t.sum f) x := by
        exact metric_mdiffAt_finset_sum (I := I) t f hft
      calc
        extDerivFun (I := I) ((insert i t).sum f) x v
            = extDerivFun (I := I) (f i + t.sum f) x v := by
              simp [Finset.sum_insert, hit]
        _ = extDerivFun (I := I) (f i) x v +
              extDerivFun (I := I) (t.sum f) x v := by
              have hadd := congr($(extDerivFun_add
                (I := I) (g := f i) (g' := t.sum f)
                (x := x) hfi hsum) v)
              simpa [Pi.add_apply] using hadd
        _ = (insert i t).sum (fun j => extDerivFun (I := I) (f j) x v) := by
              rw [ih hft]
              simp [Finset.sum_insert, hit]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [IsManifold I 1 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem metric_extDerivFun_mul
    {f g : M -> Real} {x : M} (v : TangentSpace I x)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hg : MDifferentiableAt I 𝓘(Real, Real) g x) :
    extDerivFun (I := I) (fun y : M => f y * g y) x v =
      f x * extDerivFun (I := I) g x v +
        extDerivFun (I := I) f x v * g x := by
  change extDerivFun (I := I) (f • g) x v =
      f x * extDerivFun (I := I) g x v +
        extDerivFun (I := I) f x v * g x
  have hprod := fromTangentSpace_mfderiv_smul_apply
    (I := I) (f := f) (g := g) hf hg v
  simpa [extDerivFun, Pi.smul_apply, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
    using hprod

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [IsManifold I 1 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem metric_extDerivFun_congr_eventually
    {f g : M -> Real} {x : M} (v : TangentSpace I x)
    (h : f =ᶠ[nhds x] g) :
    extDerivFun (I := I) f x v = extDerivFun (I := I) g x v := by
  have hmf := Filter.EventuallyEq.mfderiv_eq (I := I) (I' := 𝓘(Real, Real)) h
  have hx : f x = g x := h.eq_of_nhds
  unfold extDerivFun
  rw [hmf, hx]

omit [SigmaCompactSpace M] in
theorem inverseMetric_derivative_row_eq
    [DecidableEq Idx]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (gInvDt : Real -> M -> Idx -> Idx -> Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    {u : Set M}
    (hdt : InverseMetricDerivativeComponentsOn (D := D) gInv gInvDt)
    (hinv : InvMetricLocal (I := I) S gInv frame u)
    (hunique : forall t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D,
      UniqueDiffWithinAt Real D.carrier (t : Real))
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (x : M) (hx : x ∈ u) (i j : Idx) :
    (∑ a : Idx,
        (gInvDt (t : Real) x i a *
          metricCompInFrame (I := I) S frame (t : Real) x a j +
        gInv (t : Real) x i a *
          ((-2 : Real) * ricciCompInFrame (I := I) S frame (t : Real) x a j))) =
      0 := by
  let lhs : Real -> Real :=
    fun s => ∑ a : Idx,
      gInv s x i a * metricCompInFrame (I := I) S frame s x a j
  have hlhs :
      HasDerivWithinAt lhs
        (∑ a : Idx,
          (gInvDt (t : Real) x i a *
            metricCompInFrame (I := I) S frame (t : Real) x a j +
          gInv (t : Real) x i a *
            ((-2 : Real) * ricciCompInFrame (I := I) S frame (t : Real) x a j)))
        D.carrier
        (t : Real) := by
    dsimp [lhs]
    simpa [Finset.sum_apply] using
      (HasDerivWithinAt.fun_sum
        (u := (Finset.univ : Finset Idx))
        (A := fun a s =>
          gInv s x i a * metricCompInFrame (I := I) S frame s x a j)
        (A' := fun a =>
          (gInvDt (t : Real) x i a *
            metricCompInFrame (I := I) S frame (t : Real) x a j +
          gInv (t : Real) x i a *
            ((-2 : Real) * ricciCompInFrame (I := I) S frame (t : Real) x a j)))
        (s := D.carrier) (x := (t : Real))
        (fun a _ha =>
          by
            exact (hdt t x i a).mul
              (metricCompInFrame_hasDerivWithinAt (I := I) S hS frame t x a j)))
  have hconst :
      HasDerivWithinAt lhs 0 D.carrier (t : Real) := by
    dsimp [lhs]
    exact
      (hasDerivWithinAt_const
        (x := (t : Real)) (s := D.carrier)
        (c := (if i = j then 1 else 0 : Real))).congr
        (fun s _hs => by
          exact (hinv s x hx i j).1)
        (by
          exact (hinv (t : Real) x hx i j).1)
  have h1 := hlhs.derivWithin (hunique t)
  have h0 := hconst.derivWithin (hunique t)
  exact h1.symm.trans h0

theorem inverseMetric_derivative_solve
    [DecidableEq Idx]
    (metric ric gInv gInvDt : Idx -> Idx -> Real)
    (i : Idx)
    (hrow : forall j : Idx,
      (∑ a : Idx,
        (gInvDt i a * metric a j + gInv i a * ((-2 : Real) * ric a j))) = 0)
    (hleft : forall a b : Idx,
      (∑ k : Idx, gInv a k * metric k b) = (if a = b then 1 else 0))
    (hright : forall a b : Idx,
      (∑ k : Idx, metric a k * gInv k b) = (if a = b then 1 else 0))
    (hmetric_symm : forall a b : Idx, metric a b = metric b a)
    (j : Idx) :
    gInvDt i j =
      2 * (∑ a : Idx, ∑ b : Idx, gInv i a * gInv j b * ric a b) := by
  classical
  have hsymm : forall a b : Idx, gInv a b = gInv b a := by
    intro a b
    let A : Matrix Idx Idx Real := fun i j => gInv i j
    let G : Matrix Idx Idx Real := fun i j => metric i j
    have hAG : A * G = 1 := by
      ext p q
      simpa [A, G, Matrix.mul_apply] using hleft p q
    have hGA : G * A = 1 := by
      ext p q
      simpa [A, G, Matrix.mul_apply] using hright p q
    have hGt : Matrix.transpose G = G := by
      ext p q
      simpa [G] using hmetric_symm q p
    have hAtG : Matrix.transpose A * G = 1 := by
      calc
        Matrix.transpose A * G = Matrix.transpose A * Matrix.transpose G := by rw [hGt]
        _ = Matrix.transpose (G * A) := by rw [Matrix.transpose_mul]
        _ = 1 := by rw [hGA]; simp
    have hAt : Matrix.transpose A = A := by
      calc
        Matrix.transpose A = Matrix.transpose A * 1 := by simp
        _ = Matrix.transpose A * (G * A) := by rw [hGA]
        _ = (Matrix.transpose A * G) * A := by rw [← Matrix.mul_assoc]
        _ = 1 * A := by rw [hAtG]
        _ = A := by simp
    have hentry := congrArg (fun B : Matrix Idx Idx Real => B b a) hAt
    simpa [A] using hentry
  have hrow' : forall m : Idx,
      (∑ a : Idx, gInvDt i a * metric a m) =
        2 * (∑ a : Idx, gInv i a * ric a m) := by
    intro m
    have hm := hrow m
    rw [Finset.sum_add_distrib] at hm
    have hm' :
        (∑ a : Idx, gInvDt i a * metric a m) +
            (-2 : Real) * (∑ a : Idx, gInv i a * ric a m) = 0 := by
      simpa [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] using hm
    linarith
  calc
    gInvDt i j
        = ∑ a : Idx, gInvDt i a * (if a = j then 1 else 0) := by
            simp
    _ = ∑ a : Idx, gInvDt i a *
          (∑ k : Idx, metric a k * gInv k j) := by
            refine Finset.sum_congr rfl fun a _ha => ?_
            rw [hright a j]
    _ = ∑ k : Idx, (∑ a : Idx, gInvDt i a * metric a k) * gInv k j := by
            calc
              (∑ a : Idx, gInvDt i a *
                  (∑ k : Idx, metric a k * gInv k j))
                  =
                ∑ a : Idx, ∑ k : Idx,
                  gInvDt i a * (metric a k * gInv k j) := by
                    refine Finset.sum_congr rfl fun a _ha => ?_
                    rw [Finset.mul_sum]
              _ = ∑ k : Idx, ∑ a : Idx,
                  gInvDt i a * (metric a k * gInv k j) := by
                    rw [Finset.sum_comm]
              _ = ∑ k : Idx, (∑ a : Idx, gInvDt i a * metric a k) * gInv k j := by
                    refine Finset.sum_congr rfl fun k _hk => ?_
                    rw [Finset.sum_mul]
                    refine Finset.sum_congr rfl fun a _ha => ?_
                    ring
    _ = ∑ k : Idx, (2 * (∑ a : Idx, gInv i a * ric a k)) * gInv k j := by
            refine Finset.sum_congr rfl fun k _hk => ?_
            rw [hrow' k]
    _ = 2 * (∑ a : Idx, ∑ b : Idx, gInv i a * gInv j b * ric a b) := by
            calc
              (∑ k : Idx, (2 * (∑ a : Idx, gInv i a * ric a k)) * gInv k j)
                  =
                2 * (∑ k : Idx, (∑ a : Idx, gInv i a * ric a k) * gInv k j) := by
                  rw [Finset.mul_sum]
                  refine Finset.sum_congr rfl fun k _hk => ?_
                  ring
              _ = 2 * (∑ a : Idx, ∑ b : Idx, gInv i a * gInv j b * ric a b) := by
                  congr 1
                  calc
                    (∑ k : Idx, (∑ a : Idx, gInv i a * ric a k) * gInv k j)
                        =
                      ∑ k : Idx, ∑ a : Idx,
                        (gInv i a * ric a k) * gInv k j := by
                          refine Finset.sum_congr rfl fun k _hk => ?_
                          rw [Finset.sum_mul]
                    _ = ∑ a : Idx, ∑ b : Idx,
                        (gInv i a * ric a b) * gInv b j := by
                          rw [Finset.sum_comm]
                    _ = ∑ a : Idx, ∑ b : Idx,
                        gInv i a * gInv j b * ric a b := by
                          refine Finset.sum_congr rfl fun a _ha => ?_
                          refine Finset.sum_congr rfl fun b _hb => ?_
                          rw [hsymm b j]
                          ring







omit [SigmaCompactSpace M] [T2Space M] in
theorem inverseMetricCovDerivCompInFrame_eq_zero
    [DecidableEq Idx]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hinv : InvMetricLocal (I := I) S gInv frame u)
    (t : Real)
    (hmc : DifferentialGeometry.Integral.Connection.IsMetricCompatible_gen (I := I)
      cov (S.family.metric t))
    (hu : IsOpen u) {x : M} (hx : x ∈ u)
    (hginv_mdiff : ∀ a b : Idx,
      MDifferentiableAt I 𝓘(Real, Real) (fun y : M => gInv t y a b) x)
    (hmetric_mdiff : ∀ a b : Idx,
      MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => metricCompInFrame (I := I) S frame t y a b) x)
    (d k l : Idx) :
    inverseMetricCovDerivCompInFrame (I := I) gInv cov frame hframe t x d k l = 0 := by
  classical
  let G : Idx -> Idx -> Real := fun a b =>
    metricCompInFrame (I := I) S frame t x a b
  let U : Idx -> Idx -> Real := fun a b => gInv t x a b
  let DG : Idx -> Idx -> Real := fun a b =>
    extDerivFun (I := I)
      (fun y : M => metricCompInFrame (I := I) S frame t y a b)
      x (frame d x)
  let DU : Idx -> Idx -> Real := fun a b =>
    extDerivFun (I := I) (fun y : M => gInv t y a b) x (frame d x)
  let Γ : Idx -> Idx -> Real := fun a b =>
    christoffelSymbolInFrame cov frame hframe x d a b
  have hinvAt :
      Tensor0SBundle.MetricInverseInBasis_gen
        (I := I) (M := M) (S.family.metric t) x
        (hframe.toBasisAt hx) (fun a b : Idx => gInv t x a b) := by
    intro a b
    constructor
    · simpa [metricCompInFrame, IsLocalFrameOn.toBasisAt_coe] using
        (hinv t x hx a b).1
    · simpa [metricCompInFrame, IsLocalFrameOn.toBasisAt_coe] using
        (hinv t x hx a b).2
  have hsymm : ∀ a b : Idx, U a b = U b a := by
    intro a b
    simpa [U] using
      Tensor0SBundle.invMetric_symm (I := I) (M := M) (S.family.metric t)
        x (hframe.toBasisAt hx) (fun a b : Idx => gInv t x a b) hinvAt a b
  have hDG : ∀ a b : Idx,
      DG a b =
        (∑ p : Idx, Γ a p * G p b) +
          (∑ p : Idx, Γ b p * G a p) := by
    intro a b
    simpa [DG, G, Γ] using
      metricCompInFrame_extDerivFun_eq_christoffel
        (I := I) S cov t (S.family.metric t) hmc rfl frame hframe hu hx d a b
  have hrow : ∀ m : Idx,
      (∑ a : Idx, (DU k a * G a m + U k a * DG a m)) = 0 := by
    intro m
    let F : Idx -> M -> Real := fun a y =>
      gInv t y k a * metricCompInFrame (I := I) S frame t y a m
    have hF_mdiff : ∀ a ∈ (Finset.univ : Finset Idx),
        MDifferentiableAt I 𝓘(Real, Real) (F a) x := by
      intro a _ha
      exact (hginv_mdiff k a).mul (hmetric_mdiff a m)
    have hsum :
        extDerivFun (I := I) ((Finset.univ : Finset Idx).sum F) x (frame d x) =
          ∑ a : Idx, extDerivFun (I := I) (F a) x (frame d x) := by
      simpa using metric_extDerivFun_finset_sum
        (I := I) (t := (Finset.univ : Finset Idx)) F (frame d x) hF_mdiff
    have hprod : ∀ a : Idx,
        extDerivFun (I := I) (F a) x (frame d x) =
          gInv t x k a * DG a m + DU k a * G a m := by
      intro a
      simpa [F, DG, DU, G, mul_comm, mul_left_comm, mul_assoc] using
        metric_extDerivFun_mul (I := I) (x := x) (frame d x)
          (hginv_mdiff k a) (hmetric_mdiff a m)
    have hconst :
        (fun y : M => ∑ a : Idx,
          gInv t y k a * metricCompInFrame (I := I) S frame t y a m) =ᶠ[nhds x]
        (fun _ : M => if k = m then 1 else 0) := by
      filter_upwards [hu.mem_nhds hx] with y hy
      exact (hinv t y hy k m).1
    have hzero_raw :
        extDerivFun (I := I)
          (fun y : M => ∑ a : Idx,
            gInv t y k a * metricCompInFrame (I := I) S frame t y a m)
          x (frame d x) = 0 := by
      have hderiv :=
        metric_extDerivFun_congr_eventually (I := I) (x := x)
          (v := frame d x) hconst
      simpa using hderiv
    have hF_eq :
        ((Finset.univ : Finset Idx).sum F) =
          (fun y : M => ∑ a : Idx,
            gInv t y k a * metricCompInFrame (I := I) S frame t y a m) := by
      funext y
      simp [F]
    have hzero :
        extDerivFun (I := I) ((Finset.univ : Finset Idx).sum F) x (frame d x) = 0 := by
      rw [hF_eq]
      exact hzero_raw
    calc
      (∑ a : Idx, (DU k a * G a m + U k a * DG a m))
          = ∑ a : Idx, (gInv t x k a * DG a m + DU k a * G a m) := by
              simp [U, add_comm]
      _ = ∑ a : Idx, extDerivFun (I := I) (F a) x (frame d x) := by
              refine Finset.sum_congr rfl fun a _ha => ?_
              rw [hprod a]
      _ = extDerivFun (I := I) ((Finset.univ : Finset Idx).sum F) x (frame d x) := hsum.symm
      _ = 0 := hzero
  have hsolve := inverseMetric_derivative_solve
    (metric := G)
    (ric := fun a b : Idx => (-1 / 2 : Real) * DG a b)
    (gInv := U)
    (gInvDt := DU)
    k
    (by
      intro m
      calc
        (∑ a : Idx,
            (DU k a * G a m +
              U k a * ((-2 : Real) * ((-1 / 2 : Real) * DG a m)))) =
            ∑ a : Idx, (DU k a * G a m + U k a * DG a m) := by
              refine Finset.sum_congr rfl fun a _ha => ?_
              ring
        _ = 0 := hrow m)
    (by
      intro a b
      simpa [G, U] using (hinv t x hx a b).1)
    (by
      intro a b
      simpa [G, U] using (hinv t x hx a b).2)
    (by
      intro a b
      simpa [G, metricCompInFrame] using
        (S.family.metric t).symm x (frame a x) (frame b x))
    l
  have hUG_left : ∀ p : Idx,
      (∑ a : Idx, U k a * G a p) = (if k = p then 1 else 0) := by
    intro p
    simpa [U, G] using (hinv t x hx k p).1
  have hUG_right_sym : ∀ p : Idx,
      (∑ b : Idx, U l b * G p b) = (if p = l then 1 else 0) := by
    intro p
    calc
      (∑ b : Idx, U l b * G p b)
          = ∑ b : Idx, G p b * U b l := by
              refine Finset.sum_congr rfl fun b _hb => ?_
              change U l b * G p b = G p b * U b l
              rw [hsymm l b]
              ring
      _ = (if p = l then 1 else 0) := by
              simpa [U, G] using (hinv t x hx p l).2
  have hterm1 :
      (∑ a : Idx, ∑ b : Idx,
        U k a * U l b * (∑ p : Idx, Γ a p * G p b)) =
        ∑ a : Idx, Γ a l * U k a := by
    calc
      (∑ a : Idx, ∑ b : Idx,
        U k a * U l b * (∑ p : Idx, Γ a p * G p b))
          =
        ∑ a : Idx, ∑ p : Idx, U k a * Γ a p *
          (∑ b : Idx, U l b * G p b) := by
            refine Finset.sum_congr rfl fun a _ha => ?_
            calc
              (∑ b : Idx, U k a * U l b *
                (∑ p : Idx, Γ a p * G p b))
                  =
                ∑ b : Idx, ∑ p : Idx,
                  U k a * U l b * (Γ a p * G p b) := by
                    refine Finset.sum_congr rfl fun b _hb => ?_
                    rw [Finset.mul_sum]
              _ = ∑ p : Idx, ∑ b : Idx,
                  U k a * U l b * (Γ a p * G p b) := by
                    rw [Finset.sum_comm]
              _ = ∑ p : Idx, U k a * Γ a p *
                  (∑ b : Idx, U l b * G p b) := by
                    refine Finset.sum_congr rfl fun p _hp => ?_
                    rw [Finset.mul_sum]
                    refine Finset.sum_congr rfl fun b _hb => ?_
                    ring
      _ = ∑ a : Idx, ∑ p : Idx,
          U k a * Γ a p * (if p = l then 1 else 0) := by
            refine Finset.sum_congr rfl fun a _ha => ?_
            refine Finset.sum_congr rfl fun p _hp => ?_
            rw [hUG_right_sym p]
      _ = ∑ a : Idx, U k a * Γ a l := by
            refine Finset.sum_congr rfl fun a _ha => ?_
            simp
      _ = ∑ a : Idx, Γ a l * U k a := by
            refine Finset.sum_congr rfl fun a _ha => ?_
            ring
  have hterm2 :
      (∑ a : Idx, ∑ b : Idx,
        U k a * U l b * (∑ p : Idx, Γ b p * G a p)) =
        ∑ a : Idx, Γ a k * U a l := by
    calc
      (∑ a : Idx, ∑ b : Idx,
        U k a * U l b * (∑ p : Idx, Γ b p * G a p))
          =
        ∑ b : Idx, ∑ p : Idx, U l b * Γ b p *
          (∑ a : Idx, U k a * G a p) := by
            calc
              (∑ a : Idx, ∑ b : Idx,
                U k a * U l b * (∑ p : Idx, Γ b p * G a p))
                  =
                ∑ b : Idx, ∑ a : Idx,
                  U k a * U l b * (∑ p : Idx, Γ b p * G a p) := by
                    rw [Finset.sum_comm]
              _ = ∑ b : Idx, ∑ p : Idx, U l b * Γ b p *
                  (∑ a : Idx, U k a * G a p) := by
                    refine Finset.sum_congr rfl fun b _hb => ?_
                    calc
                      (∑ a : Idx, U k a * U l b *
                        (∑ p : Idx, Γ b p * G a p))
                          =
                        ∑ a : Idx, ∑ p : Idx,
                          U k a * U l b * (Γ b p * G a p) := by
                            refine Finset.sum_congr rfl fun a _ha => ?_
                            rw [Finset.mul_sum]
                      _ = ∑ p : Idx, ∑ a : Idx,
                          U k a * U l b * (Γ b p * G a p) := by
                            rw [Finset.sum_comm]
                      _ = ∑ p : Idx, U l b * Γ b p *
                          (∑ a : Idx, U k a * G a p) := by
                            refine Finset.sum_congr rfl fun p _hp => ?_
                            rw [Finset.mul_sum]
                            refine Finset.sum_congr rfl fun a _ha => ?_
                            ring
      _ = ∑ b : Idx, ∑ p : Idx,
          U l b * Γ b p * (if k = p then 1 else 0) := by
            refine Finset.sum_congr rfl fun b _hb => ?_
            refine Finset.sum_congr rfl fun p _hp => ?_
            rw [hUG_left p]
      _ = ∑ b : Idx, U l b * Γ b k := by
            refine Finset.sum_congr rfl fun b _hb => ?_
            simp
      _ = ∑ a : Idx, Γ a k * U a l := by
            refine Finset.sum_congr rfl fun a _ha => ?_
            change U l a * Γ a k = Γ a k * U a l
            rw [hsymm l a]
            ring
  have htrace :
      (∑ a : Idx, ∑ b : Idx, U k a * U l b * DG a b) =
        (∑ a : Idx, Γ a l * U k a) + (∑ a : Idx, Γ a k * U a l) := by
    calc
      (∑ a : Idx, ∑ b : Idx, U k a * U l b * DG a b)
          =
        ∑ a : Idx, ∑ b : Idx,
          U k a * U l b *
            ((∑ p : Idx, Γ a p * G p b) +
              (∑ p : Idx, Γ b p * G a p)) := by
            refine Finset.sum_congr rfl fun a _ha => ?_
            refine Finset.sum_congr rfl fun b _hb => ?_
            rw [hDG a b]
      _ =
        (∑ a : Idx, ∑ b : Idx,
          U k a * U l b * (∑ p : Idx, Γ a p * G p b)) +
        (∑ a : Idx, ∑ b : Idx,
          U k a * U l b * (∑ p : Idx, Γ b p * G a p)) := by
            simp [mul_add, Finset.sum_add_distrib]
      _ = (∑ a : Idx, Γ a l * U k a) +
          (∑ a : Idx, Γ a k * U a l) := by
            rw [hterm1, hterm2]
  have hDU :
      DU k l =
        - ((∑ a : Idx, Γ a l * U k a) + (∑ a : Idx, Γ a k * U a l)) := by
    calc
      DU k l =
          2 * (∑ a : Idx, ∑ b : Idx,
            U k a * U l b * ((-1 / 2 : Real) * DG a b)) := hsolve
      _ = - (∑ a : Idx, ∑ b : Idx, U k a * U l b * DG a b) := by
            calc
              2 * (∑ a : Idx, ∑ b : Idx,
                U k a * U l b * ((-1 / 2 : Real) * DG a b))
                  =
                ∑ a : Idx, ∑ b : Idx,
                  2 * (U k a * U l b * ((-1 / 2 : Real) * DG a b)) := by
                    rw [Finset.mul_sum]
                    refine Finset.sum_congr rfl fun a _ha => ?_
                    rw [Finset.mul_sum]
              _ = ∑ a : Idx, ∑ b : Idx,
                  -(U k a * U l b * DG a b) := by
                    refine Finset.sum_congr rfl fun a _ha => ?_
                    refine Finset.sum_congr rfl fun b _hb => ?_
                    ring
              _ = - (∑ a : Idx, ∑ b : Idx, U k a * U l b * DG a b) := by
                    rw [← Finset.sum_neg_distrib]
                    refine Finset.sum_congr rfl fun a _ha => ?_
                    rw [← Finset.sum_neg_distrib]
      _ = - ((∑ a : Idx, Γ a l * U k a) +
          (∑ a : Idx, Γ a k * U a l)) := by
            rw [htrace]
  unfold inverseMetricCovDerivCompInFrame
  change DU k l + (∑ a : Idx, Γ a k * U a l) +
      (∑ a : Idx, Γ a l * U k a) = 0
  rw [hDU]
  ring



omit [SigmaCompactSpace M] [T2Space M] in
theorem invCovZeroLocal
    [DecidableEq Idx]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hinv : InvMetricLocal (I := I) S gInv frame u)
    (t : Real)
    (hmc : DifferentialGeometry.Integral.Connection.IsMetricCompatible_gen (I := I)
      cov (S.family.metric t))
    (hu : IsOpen u) {x : M} (hx : x ∈ u)
    (hginv_mdiff : ∀ a b : Idx,
      MDifferentiableAt I 𝓘(Real, Real) (fun y : M => gInv t y a b) x)
    (hmetric_mdiff : ∀ a b : Idx,
      MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => metricCompInFrame (I := I) S frame t y a b) x)
    (d k l : Idx) :
    inverseMetricCovDerivCompInFrame (I := I) gInv cov frame hframe t x d k l = 0 := by
  classical
  let G : Idx -> Idx -> Real := fun a b =>
    metricCompInFrame (I := I) S frame t x a b
  let U : Idx -> Idx -> Real := fun a b => gInv t x a b
  let DG : Idx -> Idx -> Real := fun a b =>
    extDerivFun (I := I)
      (fun y : M => metricCompInFrame (I := I) S frame t y a b)
      x (frame d x)
  let DU : Idx -> Idx -> Real := fun a b =>
    extDerivFun (I := I) (fun y : M => gInv t y a b) x (frame d x)
  let Γ : Idx -> Idx -> Real := fun a b =>
    christoffelSymbolInFrame cov frame hframe x d a b
  have hinvAt :
      Tensor0SBundle.MetricInverseInBasis_gen
        (I := I) (M := M) (S.family.metric t) x
        (hframe.toBasisAt hx) (fun a b : Idx => gInv t x a b) := by
    intro a b
    constructor
    · simpa [metricCompInFrame, IsLocalFrameOn.toBasisAt_coe] using
        (hinv t x hx a b).1
    · simpa [metricCompInFrame, IsLocalFrameOn.toBasisAt_coe] using
        (hinv t x hx a b).2
  have hsymm : ∀ a b : Idx, U a b = U b a := by
    intro a b
    simpa [U] using
      Tensor0SBundle.invMetric_symm (I := I) (M := M) (S.family.metric t)
        x (hframe.toBasisAt hx) (fun a b : Idx => gInv t x a b) hinvAt a b
  have hDG : ∀ a b : Idx,
      DG a b =
        (∑ p : Idx, Γ a p * G p b) +
          (∑ p : Idx, Γ b p * G a p) := by
    intro a b
    simpa [DG, G, Γ] using
      metricCompInFrame_extDerivFun_eq_christoffel
        (I := I) S cov t (S.family.metric t) hmc rfl frame hframe hu hx d a b
  have hrow : ∀ m : Idx,
      (∑ a : Idx, (DU k a * G a m + U k a * DG a m)) = 0 := by
    intro m
    let F : Idx -> M -> Real := fun a y =>
      gInv t y k a * metricCompInFrame (I := I) S frame t y a m
    have hF_mdiff : ∀ a ∈ (Finset.univ : Finset Idx),
        MDifferentiableAt I 𝓘(Real, Real) (F a) x := by
      intro a _ha
      exact (hginv_mdiff k a).mul (hmetric_mdiff a m)
    have hsum :
        extDerivFun (I := I) ((Finset.univ : Finset Idx).sum F) x (frame d x) =
          ∑ a : Idx, extDerivFun (I := I) (F a) x (frame d x) := by
      simpa using metric_extDerivFun_finset_sum
        (I := I) (t := (Finset.univ : Finset Idx)) F (frame d x) hF_mdiff
    have hprod : ∀ a : Idx,
        extDerivFun (I := I) (F a) x (frame d x) =
          gInv t x k a * DG a m + DU k a * G a m := by
      intro a
      simpa [F, DG, DU, G, mul_comm, mul_left_comm, mul_assoc] using
        metric_extDerivFun_mul (I := I) (x := x) (frame d x)
          (hginv_mdiff k a) (hmetric_mdiff a m)
    have hconst :
        (fun y : M => ∑ a : Idx,
          gInv t y k a * metricCompInFrame (I := I) S frame t y a m) =ᶠ[nhds x]
        (fun _ : M => if k = m then 1 else 0) := by
      filter_upwards [hu.mem_nhds hx] with y hy
      exact (hinv t y hy k m).1
    have hzero_raw :
        extDerivFun (I := I)
          (fun y : M => ∑ a : Idx,
            gInv t y k a * metricCompInFrame (I := I) S frame t y a m)
          x (frame d x) = 0 := by
      have hderiv :=
        metric_extDerivFun_congr_eventually (I := I) (x := x)
          (v := frame d x) hconst
      simpa using hderiv
    have hF_eq :
        ((Finset.univ : Finset Idx).sum F) =
          (fun y : M => ∑ a : Idx,
            gInv t y k a * metricCompInFrame (I := I) S frame t y a m) := by
      funext y
      simp [F]
    have hzero :
        extDerivFun (I := I) ((Finset.univ : Finset Idx).sum F) x (frame d x) = 0 := by
      rw [hF_eq]
      exact hzero_raw
    calc
      (∑ a : Idx, (DU k a * G a m + U k a * DG a m))
          = ∑ a : Idx, (gInv t x k a * DG a m + DU k a * G a m) := by
              simp [U, add_comm]
      _ = ∑ a : Idx, extDerivFun (I := I) (F a) x (frame d x) := by
              refine Finset.sum_congr rfl fun a _ha => ?_
              rw [hprod a]
      _ = extDerivFun (I := I) ((Finset.univ : Finset Idx).sum F) x (frame d x) := hsum.symm
      _ = 0 := hzero
  have hsolve := inverseMetric_derivative_solve
    (metric := G)
    (ric := fun a b : Idx => (-1 / 2 : Real) * DG a b)
    (gInv := U)
    (gInvDt := DU)
    k
    (by
      intro m
      calc
        (∑ a : Idx,
            (DU k a * G a m +
              U k a * ((-2 : Real) * ((-1 / 2 : Real) * DG a m)))) =
            ∑ a : Idx, (DU k a * G a m + U k a * DG a m) := by
              refine Finset.sum_congr rfl fun a _ha => ?_
              ring
        _ = 0 := hrow m)
    (by
      intro a b
      simpa [G, U] using (hinv t x hx a b).1)
    (by
      intro a b
      simpa [G, U] using (hinv t x hx a b).2)
    (by
      intro a b
      simpa [G, metricCompInFrame] using
        (S.family.metric t).symm x (frame a x) (frame b x))
    l
  have hUG_left : ∀ p : Idx,
      (∑ a : Idx, U k a * G a p) = (if k = p then 1 else 0) := by
    intro p
    simpa [U, G] using (hinv t x hx k p).1
  have hUG_right_sym : ∀ p : Idx,
      (∑ b : Idx, U l b * G p b) = (if p = l then 1 else 0) := by
    intro p
    calc
      (∑ b : Idx, U l b * G p b)
          = ∑ b : Idx, G p b * U b l := by
              refine Finset.sum_congr rfl fun b _hb => ?_
              change U l b * G p b = G p b * U b l
              rw [hsymm l b]
              ring
      _ = (if p = l then 1 else 0) := by
              simpa [U, G] using (hinv t x hx p l).2
  have hterm1 :
      (∑ a : Idx, ∑ b : Idx,
        U k a * U l b * (∑ p : Idx, Γ a p * G p b)) =
        ∑ a : Idx, Γ a l * U k a := by
    calc
      (∑ a : Idx, ∑ b : Idx,
        U k a * U l b * (∑ p : Idx, Γ a p * G p b))
          =
        ∑ a : Idx, ∑ p : Idx, U k a * Γ a p *
          (∑ b : Idx, U l b * G p b) := by
            refine Finset.sum_congr rfl fun a _ha => ?_
            calc
              (∑ b : Idx, U k a * U l b *
                (∑ p : Idx, Γ a p * G p b))
                  =
                ∑ b : Idx, ∑ p : Idx,
                  U k a * U l b * (Γ a p * G p b) := by
                    refine Finset.sum_congr rfl fun b _hb => ?_
                    rw [Finset.mul_sum]
              _ = ∑ p : Idx, ∑ b : Idx,
                  U k a * U l b * (Γ a p * G p b) := by
                    rw [Finset.sum_comm]
              _ = ∑ p : Idx, U k a * Γ a p *
                  (∑ b : Idx, U l b * G p b) := by
                    refine Finset.sum_congr rfl fun p _hp => ?_
                    rw [Finset.mul_sum]
                    refine Finset.sum_congr rfl fun b _hb => ?_
                    ring
      _ = ∑ a : Idx, ∑ p : Idx,
          U k a * Γ a p * (if p = l then 1 else 0) := by
            refine Finset.sum_congr rfl fun a _ha => ?_
            refine Finset.sum_congr rfl fun p _hp => ?_
            rw [hUG_right_sym p]
      _ = ∑ a : Idx, U k a * Γ a l := by
            refine Finset.sum_congr rfl fun a _ha => ?_
            simp
      _ = ∑ a : Idx, Γ a l * U k a := by
            refine Finset.sum_congr rfl fun a _ha => ?_
            ring
  have hterm2 :
      (∑ a : Idx, ∑ b : Idx,
        U k a * U l b * (∑ p : Idx, Γ b p * G a p)) =
        ∑ a : Idx, Γ a k * U a l := by
    calc
      (∑ a : Idx, ∑ b : Idx,
        U k a * U l b * (∑ p : Idx, Γ b p * G a p))
          =
        ∑ b : Idx, ∑ p : Idx, U l b * Γ b p *
          (∑ a : Idx, U k a * G a p) := by
            calc
              (∑ a : Idx, ∑ b : Idx,
                U k a * U l b * (∑ p : Idx, Γ b p * G a p))
                  =
                ∑ b : Idx, ∑ a : Idx,
                  U k a * U l b * (∑ p : Idx, Γ b p * G a p) := by
                    rw [Finset.sum_comm]
              _ = ∑ b : Idx, ∑ p : Idx, U l b * Γ b p *
                  (∑ a : Idx, U k a * G a p) := by
                    refine Finset.sum_congr rfl fun b _hb => ?_
                    calc
                      (∑ a : Idx, U k a * U l b *
                        (∑ p : Idx, Γ b p * G a p))
                          =
                        ∑ a : Idx, ∑ p : Idx,
                          U k a * U l b * (Γ b p * G a p) := by
                            refine Finset.sum_congr rfl fun a _ha => ?_
                            rw [Finset.mul_sum]
                      _ = ∑ p : Idx, ∑ a : Idx,
                          U k a * U l b * (Γ b p * G a p) := by
                            rw [Finset.sum_comm]
                      _ = ∑ p : Idx, U l b * Γ b p *
                          (∑ a : Idx, U k a * G a p) := by
                            refine Finset.sum_congr rfl fun p _hp => ?_
                            rw [Finset.mul_sum]
                            refine Finset.sum_congr rfl fun a _ha => ?_
                            ring
      _ = ∑ b : Idx, ∑ p : Idx,
          U l b * Γ b p * (if k = p then 1 else 0) := by
            refine Finset.sum_congr rfl fun b _hb => ?_
            refine Finset.sum_congr rfl fun p _hp => ?_
            rw [hUG_left p]
      _ = ∑ b : Idx, U l b * Γ b k := by
            refine Finset.sum_congr rfl fun b _hb => ?_
            simp
      _ = ∑ a : Idx, Γ a k * U a l := by
            refine Finset.sum_congr rfl fun a _ha => ?_
            change U l a * Γ a k = Γ a k * U a l
            rw [hsymm l a]
            ring
  have htrace :
      (∑ a : Idx, ∑ b : Idx, U k a * U l b * DG a b) =
        (∑ a : Idx, Γ a l * U k a) + (∑ a : Idx, Γ a k * U a l) := by
    calc
      (∑ a : Idx, ∑ b : Idx, U k a * U l b * DG a b)
          =
        ∑ a : Idx, ∑ b : Idx,
          U k a * U l b *
            ((∑ p : Idx, Γ a p * G p b) +
              (∑ p : Idx, Γ b p * G a p)) := by
            refine Finset.sum_congr rfl fun a _ha => ?_
            refine Finset.sum_congr rfl fun b _hb => ?_
            rw [hDG a b]
      _ =
        (∑ a : Idx, ∑ b : Idx,
          U k a * U l b * (∑ p : Idx, Γ a p * G p b)) +
        (∑ a : Idx, ∑ b : Idx,
          U k a * U l b * (∑ p : Idx, Γ b p * G a p)) := by
            simp [mul_add, Finset.sum_add_distrib]
      _ = (∑ a : Idx, Γ a l * U k a) +
          (∑ a : Idx, Γ a k * U a l) := by
            rw [hterm1, hterm2]
  have hDU :
      DU k l =
        - ((∑ a : Idx, Γ a l * U k a) + (∑ a : Idx, Γ a k * U a l)) := by
    calc
      DU k l =
          2 * (∑ a : Idx, ∑ b : Idx,
            U k a * U l b * ((-1 / 2 : Real) * DG a b)) := hsolve
      _ = - (∑ a : Idx, ∑ b : Idx, U k a * U l b * DG a b) := by
            calc
              2 * (∑ a : Idx, ∑ b : Idx,
                U k a * U l b * ((-1 / 2 : Real) * DG a b))
                  =
                ∑ a : Idx, ∑ b : Idx,
                  2 * (U k a * U l b * ((-1 / 2 : Real) * DG a b)) := by
                    rw [Finset.mul_sum]
                    refine Finset.sum_congr rfl fun a _ha => ?_
                    rw [Finset.mul_sum]
              _ = ∑ a : Idx, ∑ b : Idx,
                  -(U k a * U l b * DG a b) := by
                    refine Finset.sum_congr rfl fun a _ha => ?_
                    refine Finset.sum_congr rfl fun b _hb => ?_
                    ring
              _ = - (∑ a : Idx, ∑ b : Idx, U k a * U l b * DG a b) := by
                    rw [← Finset.sum_neg_distrib]
                    refine Finset.sum_congr rfl fun a _ha => ?_
                    rw [← Finset.sum_neg_distrib]
      _ = - ((∑ a : Idx, Γ a l * U k a) +
          (∑ a : Idx, Γ a k * U a l)) := by
            rw [htrace]
  unfold inverseMetricCovDerivCompInFrame
  change DU k l + (∑ a : Idx, Γ a k * U a l) +
      (∑ a : Idx, Γ a l * U k a) = 0
  rw [hDU]
  ring


end Components

end DifferentialGeometry.PDE.RicciFlow
