import DifferentialGeometry.Geometry.Coordinates.MetricCompatibility.Inverse

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedFintypeInType false










namespace DifferentialGeometry.Tensor.Coordinates

noncomputable section

open Bundle
open DifferentialGeometry.Integral.Connection
open Tensor0SBundle
open scoped Manifold ContDiff BigOperators Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

section Components

variable {Idx : Type*} [Fintype Idx]
variable {u : Set M}


def InverseMetricComponentsForMetricInFrameOn [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M)
    (gInv : M -> Idx -> Idx -> Real)
    (frame : Idx -> (x : M) -> TangentSpace I x) : Prop :=
  forall x i j,
    (∑ k : Idx, gInv x i k * metricCompForMetricInFrame (I := I) g frame x k j) =
        (if i = j then 1 else 0) ∧
      (∑ k : Idx, metricCompForMetricInFrame (I := I) g frame x i k * gInv x k j) =
        (if i = j then 1 else 0)


omit [FiniteDimensional ℝ E] in
theorem gInvForMetric_symm [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M)
    (gInv : M -> Idx -> Idx -> Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hinv : InverseMetricComponentsForMetricInFrameOn (I := I) g gInv frame) :
    forall x i j, gInv x i j = gInv x j i := by
  intro x i j
  exact DifferentialGeometry.Integral.Connection.invComp_symm
    (I := I) (g := g) (gInv := gInv) frame
    (by
      intro y a b
      simpa [metricCompForMetricInFrame] using hinv y a b)
    x i j


def inverseMetricCovDerivForMetricCompInFrame
    (gInv : M -> Idx -> Idx -> Real)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (x : M) (d k l : Idx) : Real :=
  extDerivFun (I := I) (fun y : M => gInv y k l) x (frame d x) +
    (∑ a : Idx,
      christoffelSymbolInFrame cov frame hframe x d a k * gInv x a l) +
    (∑ a : Idx,
      christoffelSymbolInFrame cov frame hframe x d a l * gInv x k a)

def inverseMetricCovDerivForMetricCompAlongInFrame
    (gInv : M -> Idx -> Idx -> Real)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (x : M) (X : TangentSpace I x) (k l : Idx) : Real :=
  extDerivFun (I := I) (fun y : M => gInv y k l) x X +
    (∑ a : Idx,
      christoffelAlongInFrame cov frame hframe x X a k * gInv x a l) +
    (∑ a : Idx,
      christoffelAlongInFrame cov frame hframe x X a l * gInv x k a)

omit [FiniteDimensional ℝ E] [Fintype Idx] in
private theorem metric_localFrame_mdiffAt
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u) (i : Idx) :
    MDiffAt (T% (frame i)) x :=
  (hframe.contMDiffAt hu hx i).mdifferentiableAt one_ne_zero

omit [FiniteDimensional ℝ E] [Fintype Idx] in
theorem metricComp_mdiffAt
    (g : SmoothRiemannianMetric I M)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u) (i j : Idx) :
    MDifferentiableAt I 𝓘(Real, Real)
      (fun y : M => metricCompForMetricInFrame (I := I) g frame y i j) x := by
  have hg :
      MDifferentiableAt I
        (I.prod 𝓘(Real, E →L[Real] E →L[Real] Real))
        (fun y : M =>
          TotalSpace.mk' (E →L[Real] E →L[Real] Real)
            (E := fun y : M =>
              TangentSpace I y →L[Real] TangentSpace I y →L[Real] Real)
            y (g.inner y)) x :=
    g.contMDiff.mdifferentiableAt (by simp)
  have hi := metric_localFrame_mdiffAt (I := I) frame hframe hu hx i
  have hj := metric_localFrame_mdiffAt (I := I) frame hframe hu hx j
  have htotal :
      MDifferentiableAt I (I.prod 𝓘(Real, Real))
        (fun y : M =>
          TotalSpace.mk' Real (E := Bundle.Trivial M Real) y
            (g.inner y (frame i y) (frame j y))) x := by
    exact MDifferentiableAt.clm_bundle_apply₂
      (F₁ := E) (F₂ := E) hg hi hj
  rw [mdifferentiableAt_totalSpace] at htotal
  simpa [metricCompForMetricInFrame] using htotal.2




omit [FiniteDimensional ℝ E] in
theorem metricCompForMetricInFrame_extDerivFun_eq_christoffel
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hmc : DifferentialGeometry.Integral.Connection.IsMetricCompatible_gen (I := I) cov g)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u)
    (d a b : Idx) :
    extDerivFun (I := I)
        (fun y : M => metricCompForMetricInFrame (I := I) g frame y a b)
        x (frame d x) =
      (∑ p : Idx,
        christoffelSymbolInFrame cov frame hframe x d a p *
          metricCompForMetricInFrame (I := I) g frame x p b) +
      (∑ p : Idx,
        christoffelSymbolInFrame cov frame hframe x d b p *
          metricCompForMetricInFrame (I := I) g frame x a p) := by
  classical
  have hd := metric_localFrame_mdiffAt (I := I) frame hframe hu hx d
  have ha := metric_localFrame_mdiffAt (I := I) frame hframe hu hx a
  have hb := metric_localFrame_mdiffAt (I := I) frame hframe hu hx b
  have hmetric :=
    DifferentialGeometry.Integral.Connection.metric_compatible_apply
      (I := I) hmc (frame d) (frame a) (frame b) hd ha hb
  have hmetric' :
      extDerivFun (I := I)
          (fun y : M => metricCompForMetricInFrame (I := I) g frame y a b)
          x (frame d x) =
        g.inner x ((cov (frame a) x) (frame d x)) (frame b x) +
          g.inner x (frame a x) ((cov (frame b) x) (frame d x)) := by
    simpa [extDerivFun, metricCompForMetricInFrame] using hmetric
  rw [hmetric']
  rw [covariantDerivative_eq_sum_christoffel (I := I) cov frame hframe hx d a]
  rw [covariantDerivative_eq_sum_christoffel (I := I) cov frame hframe hx d b]
  simp [metricCompForMetricInFrame, map_sum]



omit [FiniteDimensional ℝ E] in
theorem metricComp_extDeriv_tangent
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hmc : DifferentialGeometry.Integral.Connection.IsMetricCompatible_gen (I := I) cov g)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u)
    (X : TangentSpace I x) (a b : Idx) :
    extDerivFun (I := I)
        (fun y : M => metricCompForMetricInFrame (I := I) g frame y a b)
        x X =
      (∑ p : Idx,
        christoffelAlongInFrame cov frame hframe x X a p *
          metricCompForMetricInFrame (I := I) g frame x p b) +
      (∑ p : Idx,
        christoffelAlongInFrame cov frame hframe x X b p *
          metricCompForMetricInFrame (I := I) g frame x a p) := by
  classical
  let c : Idx -> Real := fun d => hframe.coeff d x X
  let G : Idx -> Idx -> Real := fun i j =>
    metricCompForMetricInFrame (I := I) g frame x i j
  let Γ : Idx -> Idx -> Idx -> Real := fun d i j =>
    christoffelSymbolInFrame cov frame hframe x d i j
  have hX : X = ∑ d : Idx, c d • frame d x := by
    simpa [c, IsLocalFrameOn.coeff, hx, IsLocalFrameOn.toBasisAt_coe] using
      ((hframe.toBasisAt hx).sum_repr X).symm
  have hbasis (d : Idx) :
      extDerivFun (I := I)
          (fun y : M => metricCompForMetricInFrame (I := I) g frame y a b)
          x (frame d x) =
        (∑ p : Idx, Γ d a p * G p b) +
          (∑ p : Idx, Γ d b p * G a p) := by
    simpa [Γ, G] using
      metricCompForMetricInFrame_extDerivFun_eq_christoffel
        (I := I) g cov hmc frame hframe hu hx d a b
  have hAlongA (p : Idx) :
      christoffelAlongInFrame cov frame hframe x X a p =
        ∑ d : Idx, c d * Γ d a p := by
    simpa [c, Γ] using
      christoffelAlongInFrame_eq_sum_coeff
        (I := I) cov frame hframe hx X a p
  have hAlongB (p : Idx) :
      christoffelAlongInFrame cov frame hframe x X b p =
        ∑ d : Idx, c d * Γ d b p := by
    simpa [c, Γ] using
      christoffelAlongInFrame_eq_sum_coeff
        (I := I) cov frame hframe hx X b p
  have htermA :
      (∑ d : Idx, c d * (∑ p : Idx, Γ d a p * G p b)) =
        ∑ p : Idx, (∑ d : Idx, c d * Γ d a p) * G p b := by
    calc
      (∑ d : Idx, c d * (∑ p : Idx, Γ d a p * G p b))
          = ∑ d : Idx, ∑ p : Idx, c d * (Γ d a p * G p b) := by
              refine Finset.sum_congr rfl fun d _ => ?_
              rw [Finset.mul_sum]
      _ = ∑ p : Idx, ∑ d : Idx, c d * (Γ d a p * G p b) := by
              rw [Finset.sum_comm]
      _ = ∑ p : Idx, (∑ d : Idx, c d * Γ d a p) * G p b := by
              refine Finset.sum_congr rfl fun p _ => ?_
              rw [Finset.sum_mul]
              refine Finset.sum_congr rfl fun d _ => ?_
              ring
  have htermB :
      (∑ d : Idx, c d * (∑ p : Idx, Γ d b p * G a p)) =
        ∑ p : Idx, (∑ d : Idx, c d * Γ d b p) * G a p := by
    calc
      (∑ d : Idx, c d * (∑ p : Idx, Γ d b p * G a p))
          = ∑ d : Idx, ∑ p : Idx, c d * (Γ d b p * G a p) := by
              refine Finset.sum_congr rfl fun d _ => ?_
              rw [Finset.mul_sum]
      _ = ∑ p : Idx, ∑ d : Idx, c d * (Γ d b p * G a p) := by
              rw [Finset.sum_comm]
      _ = ∑ p : Idx, (∑ d : Idx, c d * Γ d b p) * G a p := by
              refine Finset.sum_congr rfl fun p _ => ?_
              rw [Finset.sum_mul]
              refine Finset.sum_congr rfl fun d _ => ?_
              ring
  calc
    extDerivFun (I := I)
        (fun y : M => metricCompForMetricInFrame (I := I) g frame y a b)
        x X
        =
      extDerivFun (I := I)
        (fun y : M => metricCompForMetricInFrame (I := I) g frame y a b)
        x (∑ d : Idx, c d • frame d x) := by
          rw [hX]
    _ = ∑ d : Idx,
          c d *
            extDerivFun (I := I)
              (fun y : M => metricCompForMetricInFrame (I := I) g frame y a b)
              x (frame d x) := by
          simp [map_sum, map_smul]
    _ = ∑ d : Idx,
          c d * ((∑ p : Idx, Γ d a p * G p b) +
            (∑ p : Idx, Γ d b p * G a p)) := by
          refine Finset.sum_congr rfl fun d _ => ?_
          rw [hbasis d]
    _ = (∑ p : Idx, (∑ d : Idx, c d * Γ d a p) * G p b) +
        (∑ p : Idx, (∑ d : Idx, c d * Γ d b p) * G a p) := by
          rw [← htermA, ← htermB]
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun d _ => ?_
          ring
    _ = (∑ p : Idx,
          christoffelAlongInFrame cov frame hframe x X a p *
            metricCompForMetricInFrame (I := I) g frame x p b) +
        (∑ p : Idx,
          christoffelAlongInFrame cov frame hframe x X b p *
            metricCompForMetricInFrame (I := I) g frame x a p) := by
          congr 1
          · refine Finset.sum_congr rfl fun p _ => ?_
            rw [hAlongA p]
          · refine Finset.sum_congr rfl fun p _ => ?_
            rw [hAlongB p]

omit [FiniteDimensional ℝ E] in
theorem metricCompForMetricInFrame_extDerivFun_eq_christoffelAlong
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hmc : DifferentialGeometry.Integral.Connection.IsMetricCompatible_gen (I := I) cov g)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u) {x : M} (hx : x ∈ u)
    (a b : Idx) :
    extDerivFun (I := I)
        (fun y : M => metricCompForMetricInFrame (I := I) g frame y a b)
        x (X x) =
      (∑ p : Idx,
        christoffelAlongInFrame cov frame hframe x (X x) a p *
          metricCompForMetricInFrame (I := I) g frame x p b) +
      (∑ p : Idx,
        christoffelAlongInFrame cov frame hframe x (X x) b p *
          metricCompForMetricInFrame (I := I) g frame x a p) := by
  classical
  have hX : MDiffAt (T% (fun y : M => X y)) x :=
    X.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have ha := metric_localFrame_mdiffAt (I := I) frame hframe hu hx a
  have hb := metric_localFrame_mdiffAt (I := I) frame hframe hu hx b
  have hmetric :=
    DifferentialGeometry.Integral.Connection.metric_compatible_apply
      (I := I) hmc (fun y : M => X y) (frame a) (frame b) hX ha hb
  have hmetric' :
      extDerivFun (I := I)
          (fun y : M => metricCompForMetricInFrame (I := I) g frame y a b)
          x (X x) =
        g.inner x ((cov (frame a) x) (X x)) (frame b x) +
          g.inner x (frame a x) ((cov (frame b) x) (X x)) := by
    simpa [extDerivFun, metricCompForMetricInFrame] using hmetric
  rw [hmetric']
  have hcov_a :
      (cov (frame a) x) (X x) =
        ∑ p : Idx, christoffelAlongInFrame cov frame hframe x (X x) a p • frame p x :=
    hframe.coeff_sum_eq (fun y => (cov (frame a) y) (X y)) hx
  have hcov_b :
      (cov (frame b) x) (X x) =
        ∑ p : Idx, christoffelAlongInFrame cov frame hframe x (X x) b p • frame p x :=
    hframe.coeff_sum_eq (fun y => (cov (frame b) y) (X y)) hx
  rw [hcov_a, hcov_b]
  simp [metricCompForMetricInFrame, map_sum]


omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem mdiffAt_finset_sum_real
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


omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem extDerivFun_finset_sum_real
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
        exact mdiffAt_finset_sum_real (I := I) t f hft
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


omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem extDerivFun_mul_real
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

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem deriv_congr_nhds
    {f g : M -> Real} {x : M} (v : TangentSpace I x)
    (h : f =ᶠ[𝓝 x] g) :
    extDerivFun (I := I) f x v = extDerivFun (I := I) g x v := by
  have hmf := Filter.EventuallyEq.mfderiv_eq (I := I) (I' := 𝓘(Real, Real)) h
  have hx : f x = g x := h.eq_of_nhds
  unfold extDerivFun
  rw [hmf, hx]

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



omit [FiniteDimensional ℝ E] in
theorem inverseMetricCovDerivForMetricCompInFrame_eq_zero
    [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M)
    (gInv : M -> Idx -> Idx -> Real)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hinv : InverseMetricComponentsForMetricInFrameOn (I := I) g gInv frame)
    (hmc : DifferentialGeometry.Integral.Connection.IsMetricCompatible_gen (I := I) cov g)
    (hu : IsOpen u) {x : M} (hx : x ∈ u)
    (hginv_mdiff : ∀ a b : Idx,
      MDifferentiableAt I 𝓘(Real, Real) (fun y : M => gInv y a b) x)
    (hmetric_mdiff : ∀ a b : Idx,
      MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => metricCompForMetricInFrame (I := I) g frame y a b) x)
    (d k l : Idx) :
    inverseMetricCovDerivForMetricCompInFrame (I := I) gInv cov frame hframe x d k l = 0 := by
  classical
  let G : Idx -> Idx -> Real := fun a b =>
    metricCompForMetricInFrame (I := I) g frame x a b
  let U : Idx -> Idx -> Real := fun a b => gInv x a b
  let DG : Idx -> Idx -> Real := fun a b =>
    extDerivFun (I := I)
      (fun y : M => metricCompForMetricInFrame (I := I) g frame y a b)
      x (frame d x)
  let DU : Idx -> Idx -> Real := fun a b =>
    extDerivFun (I := I) (fun y : M => gInv y a b) x (frame d x)
  let Γ : Idx -> Idx -> Real := fun a b =>
    christoffelSymbolInFrame cov frame hframe x d a b
  have hsymm : forall x i j, gInv x i j = gInv x j i :=
    gInvForMetric_symm (I := I) g gInv frame hinv
  have hDG : ∀ a b : Idx,
      DG a b =
        (∑ p : Idx, Γ a p * G p b) +
          (∑ p : Idx, Γ b p * G a p) := by
    intro a b
    simpa [DG, G, Γ] using
      metricCompForMetricInFrame_extDerivFun_eq_christoffel
        (I := I) g cov hmc frame hframe hu hx d a b
  have hrow : ∀ m : Idx,
      (∑ a : Idx, (DU k a * G a m + U k a * DG a m)) = 0 := by
    intro m
    let F : Idx -> M -> Real := fun a y =>
      gInv y k a * metricCompForMetricInFrame (I := I) g frame y a m
    have hF_mdiff : ∀ a ∈ (Finset.univ : Finset Idx),
        MDifferentiableAt I 𝓘(Real, Real) (F a) x := by
      intro a _ha
      exact (hginv_mdiff k a).mul (hmetric_mdiff a m)
    have hsum :
        extDerivFun (I := I) ((Finset.univ : Finset Idx).sum F) x (frame d x) =
          ∑ a : Idx, extDerivFun (I := I) (F a) x (frame d x) := by
      simpa using extDerivFun_finset_sum_real
        (I := I) (t := (Finset.univ : Finset Idx)) F (frame d x) hF_mdiff
    have hprod : ∀ a : Idx,
        extDerivFun (I := I) (F a) x (frame d x) =
          gInv x k a * DG a m + DU k a * G a m := by
      intro a
      simpa [F, DG, DU, G, mul_comm, mul_left_comm, mul_assoc] using
        extDerivFun_mul_real (I := I) (x := x) (frame d x)
          (hginv_mdiff k a) (hmetric_mdiff a m)
    have hconst :
        (fun y : M => ∑ a : Idx,
          gInv y k a * metricCompForMetricInFrame (I := I) g frame y a m) =
        (fun _ : M => if k = m then 1 else 0) := by
      funext y
      exact (hinv y k m).1
    have hderiv :=
      congrArg (fun F : M -> Real => extDerivFun (I := I) F x (frame d x)) hconst
    have hzero_raw :
        extDerivFun (I := I)
          (fun y : M => ∑ a : Idx,
            gInv y k a * metricCompForMetricInFrame (I := I) g frame y a m)
          x (frame d x) = 0 := by
      simpa using hderiv
    have hF_eq :
        ((Finset.univ : Finset Idx).sum F) =
          (fun y : M => ∑ a : Idx,
            gInv y k a * metricCompForMetricInFrame (I := I) g frame y a m) := by
      funext y
      simp [F]
    have hzero :
        extDerivFun (I := I) ((Finset.univ : Finset Idx).sum F) x (frame d x) = 0 := by
      rw [hF_eq]
      exact hzero_raw
    calc
      (∑ a : Idx, (DU k a * G a m + U k a * DG a m))
          = ∑ a : Idx, (gInv x k a * DG a m + DU k a * G a m) := by
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
      simpa [G, U] using (hinv x a b).1)
    (by
      intro a b
      simpa [G, U] using (hinv x a b).2)
    (by
      intro a b
      simpa [G, metricCompForMetricInFrame] using g.symm x (frame a x) (frame b x))
    l
  have hUG_left : ∀ p : Idx,
      (∑ a : Idx, U k a * G a p) = (if k = p then 1 else 0) := by
    intro p
    simpa [U, G] using (hinv x k p).1
  have hUG_right_sym : ∀ p : Idx,
      (∑ b : Idx, U l b * G p b) = (if p = l then 1 else 0) := by
    intro p
    calc
      (∑ b : Idx, U l b * G p b)
          = ∑ b : Idx, G p b * U b l := by
              refine Finset.sum_congr rfl fun b _hb => ?_
              change gInv x l b * G p b = G p b * gInv x b l
              rw [hsymm x l b]
              ring
      _ = (if p = l then 1 else 0) := by
              simpa [U, G] using (hinv x p l).2
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
            change gInv x l a * Γ a k = Γ a k * gInv x a l
            rw [hsymm x l a]
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
  unfold inverseMetricCovDerivForMetricCompInFrame
  change DU k l + (∑ a : Idx, Γ a k * U a l) +
      (∑ a : Idx, Γ a l * U k a) = 0
  rw [hDU]
  ring

omit [FiniteDimensional ℝ E] in
theorem inverseMetricCovDerivForMetricCompAlongInFrame_eq_zero
    [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M)
    (gInv : M -> Idx -> Idx -> Real)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hinv : InverseMetricComponentsForMetricInFrameOn (I := I) g gInv frame)
    (hmc : DifferentialGeometry.Integral.Connection.IsMetricCompatible_gen (I := I) cov g)
    (hu : IsOpen u) {x : M} (hx : x ∈ u)
    (hginv_mdiff : ∀ a b : Idx,
      MDifferentiableAt I 𝓘(Real, Real) (fun y : M => gInv y a b) x)
    (hmetric_mdiff : ∀ a b : Idx,
      MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => metricCompForMetricInFrame (I := I) g frame y a b) x)
    (k l : Idx) :
    inverseMetricCovDerivForMetricCompAlongInFrame
        (I := I) gInv cov frame hframe x (X x) k l = 0 := by
  classical
  let G : Idx -> Idx -> Real := fun a b =>
    metricCompForMetricInFrame (I := I) g frame x a b
  let U : Idx -> Idx -> Real := fun a b => gInv x a b
  let DG : Idx -> Idx -> Real := fun a b =>
    extDerivFun (I := I)
      (fun y : M => metricCompForMetricInFrame (I := I) g frame y a b)
      x (X x)
  let DU : Idx -> Idx -> Real := fun a b =>
    extDerivFun (I := I) (fun y : M => gInv y a b) x (X x)
  let Γ : Idx -> Idx -> Real := fun a b =>
    christoffelAlongInFrame cov frame hframe x (X x) a b
  have hsymm : forall x i j, gInv x i j = gInv x j i :=
    gInvForMetric_symm (I := I) g gInv frame hinv
  have hDG : ∀ a b : Idx,
      DG a b =
        (∑ p : Idx, Γ a p * G p b) +
          (∑ p : Idx, Γ b p * G a p) := by
    intro a b
    simpa [DG, G, Γ] using
      metricCompForMetricInFrame_extDerivFun_eq_christoffelAlong
        (I := I) g cov hmc X frame hframe hu hx a b
  have hrow : ∀ m : Idx,
      (∑ a : Idx, (DU k a * G a m + U k a * DG a m)) = 0 := by
    intro m
    let F : Idx -> M -> Real := fun a y =>
      gInv y k a * metricCompForMetricInFrame (I := I) g frame y a m
    have hF_mdiff : ∀ a ∈ (Finset.univ : Finset Idx),
        MDifferentiableAt I 𝓘(Real, Real) (F a) x := by
      intro a _ha
      exact (hginv_mdiff k a).mul (hmetric_mdiff a m)
    have hsum :
        extDerivFun (I := I) ((Finset.univ : Finset Idx).sum F) x (X x) =
          ∑ a : Idx, extDerivFun (I := I) (F a) x (X x) := by
      simpa using extDerivFun_finset_sum_real
        (I := I) (t := (Finset.univ : Finset Idx)) F (X x) hF_mdiff
    have hprod : ∀ a : Idx,
        extDerivFun (I := I) (F a) x (X x) =
          gInv x k a * DG a m + DU k a * G a m := by
      intro a
      simpa [F, DG, DU, G, mul_comm, mul_left_comm, mul_assoc] using
        extDerivFun_mul_real (I := I) (x := x) (X x)
          (hginv_mdiff k a) (hmetric_mdiff a m)
    have hconst :
        (fun y : M => ∑ a : Idx,
          gInv y k a * metricCompForMetricInFrame (I := I) g frame y a m) =
        (fun _ : M => if k = m then 1 else 0) := by
      funext y
      exact (hinv y k m).1
    have hderiv :=
      congrArg (fun F : M -> Real => extDerivFun (I := I) F x (X x)) hconst
    have hzero_raw :
        extDerivFun (I := I)
          (fun y : M => ∑ a : Idx,
            gInv y k a * metricCompForMetricInFrame (I := I) g frame y a m)
          x (X x) = 0 := by
      simpa using hderiv
    have hF_eq :
        ((Finset.univ : Finset Idx).sum F) =
          (fun y : M => ∑ a : Idx,
            gInv y k a * metricCompForMetricInFrame (I := I) g frame y a m) := by
      funext y
      simp [F]
    have hzero :
        extDerivFun (I := I) ((Finset.univ : Finset Idx).sum F) x (X x) = 0 := by
      rw [hF_eq]
      exact hzero_raw
    calc
      (∑ a : Idx, (DU k a * G a m + U k a * DG a m))
          = ∑ a : Idx, (gInv x k a * DG a m + DU k a * G a m) := by
              simp [U, add_comm]
      _ = ∑ a : Idx, extDerivFun (I := I) (F a) x (X x) := by
              refine Finset.sum_congr rfl fun a _ha => ?_
              rw [hprod a]
      _ = extDerivFun (I := I) ((Finset.univ : Finset Idx).sum F) x (X x) := hsum.symm
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
      simpa [G, U] using (hinv x a b).1)
    (by
      intro a b
      simpa [G, U] using (hinv x a b).2)
    (by
      intro a b
      simpa [G, metricCompForMetricInFrame] using g.symm x (frame a x) (frame b x))
    l
  have hUG_left : ∀ p : Idx,
      (∑ a : Idx, U k a * G a p) = (if k = p then 1 else 0) := by
    intro p
    simpa [U, G] using (hinv x k p).1
  have hUG_right_sym : ∀ p : Idx,
      (∑ b : Idx, U l b * G p b) = (if p = l then 1 else 0) := by
    intro p
    calc
      (∑ b : Idx, U l b * G p b)
          = ∑ b : Idx, G p b * U b l := by
              refine Finset.sum_congr rfl fun b _hb => ?_
              change gInv x l b * G p b = G p b * gInv x b l
              rw [hsymm x l b]
              ring
      _ = (if p = l then 1 else 0) := by
              simpa [U, G] using (hinv x p l).2
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
            change gInv x l a * Γ a k = Γ a k * gInv x a l
            rw [hsymm x l a]
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
  unfold inverseMetricCovDerivForMetricCompAlongInFrame
  change DU k l + (∑ a : Idx, Γ a k * U a l) +
      (∑ a : Idx, Γ a l * U k a) = 0
  rw [hDU]
  ring


end Components

end
end DifferentialGeometry.Tensor.Coordinates
