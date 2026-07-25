import DifferentialGeometry.Geometry.Coordinates.MetricCompatibility.Covariant

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

omit [FiniteDimensional ℝ E] in
theorem invCovZeroLocal
    [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M)
    (gInv : M -> Idx -> Idx -> Real)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    {x : M}
    (hinvX : ∀ i j : Idx,
      (∑ k : Idx, gInv x i k * metricCompForMetricInFrame (I := I) g frame x k j) =
          (if i = j then 1 else 0) ∧
        (∑ k : Idx, metricCompForMetricInFrame (I := I) g frame x i k * gInv x k j) =
          (if i = j then 1 else 0))
    (hinvN : ∀ i j : Idx,
      (fun y : M => ∑ k : Idx,
          gInv y i k * metricCompForMetricInFrame (I := I) g frame y k j) =ᶠ[𝓝 x]
        fun _ : M => if i = j then 1 else 0)
    (hmc : DifferentialGeometry.Integral.Connection.IsMetricCompatible_gen (I := I) cov g)
    (hu : IsOpen u) (hx : x ∈ u)
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
  have hsymmX : forall i j : Idx, gInv x i j = gInv x j i := by
    intro i j
    let A : Matrix Idx Idx Real := fun i j => gInv x i j
    let G : Matrix Idx Idx Real := fun i j =>
      metricCompForMetricInFrame (I := I) g frame x i j
    have hAG : A * G = 1 := by
      ext a b
      simpa [A, G, Matrix.mul_apply] using (hinvX a b).1
    have hGA : G * A = 1 := by
      ext a b
      simpa [A, G, Matrix.mul_apply] using (hinvX a b).2
    have hGt : Matrix.transpose G = G := by
      ext a b
      simpa [G, metricCompForMetricInFrame] using
        g.symm x (frame b x) (frame a x)
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
    have hentry := congrArg (fun B : Matrix Idx Idx Real => B j i) hAt
    simpa [A] using hentry
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
    have hzero_raw :
        extDerivFun (I := I)
          (fun y : M => ∑ a : Idx,
            gInv y k a * metricCompForMetricInFrame (I := I) g frame y a m)
          x (X x) = 0 := by
      calc
        extDerivFun (I := I)
            (fun y : M => ∑ a : Idx,
              gInv y k a * metricCompForMetricInFrame (I := I) g frame y a m)
            x (X x)
            =
          extDerivFun (I := I) (fun _ : M => if k = m then 1 else 0) x (X x) :=
            deriv_congr_nhds (I := I) (X x) (hinvN k m)
        _ = 0 := by
            simp [extDerivFun]
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
      simpa [G, U] using (hinvX a b).1)
    (by
      intro a b
      simpa [G, U] using (hinvX a b).2)
    (by
      intro a b
      simpa [G, metricCompForMetricInFrame] using g.symm x (frame a x) (frame b x))
    l
  have hUG_left : ∀ p : Idx,
      (∑ a : Idx, U k a * G a p) = (if k = p then 1 else 0) := by
    intro p
    simpa [U, G] using (hinvX k p).1
  have hUG_right_sym : ∀ p : Idx,
      (∑ b : Idx, U l b * G p b) = (if p = l then 1 else 0) := by
    intro p
    calc
      (∑ b : Idx, U l b * G p b)
          = ∑ b : Idx, G p b * U b l := by
              refine Finset.sum_congr rfl fun b _hb => ?_
              change gInv x l b * G p b = G p b * gInv x b l
              rw [hsymmX l b]
              ring
      _ = (if p = l then 1 else 0) := by
              simpa [U, G] using (hinvX p l).2
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
            refine Finset.sum_congr rfl fun b _ha => ?_
            simp
      _ = ∑ a : Idx, Γ a k * U a l := by
            refine Finset.sum_congr rfl fun a _ha => ?_
            change gInv x l a * Γ a k = Γ a k * gInv x a l
            rw [hsymmX l a]
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

theorem gInvCovZeroAt
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (hmc : DifferentialGeometry.Integral.Connection.IsMetricCompatible_gen (I := I) cov g)
    (x₀ : M) (k l : CoordinateIdx (𝕜 := Real) E) :
    inverseMetricCovDerivForMetricCompAlongInFrame
        (I := I)
        (fun y : M => fun a b : CoordinateIdx (𝕜 := Real) E =>
          inverseMetricFlatModelInChart_component (I := I) g x₀ a b
            (extChartAt I x₀ y))
        cov (coordinateFrameAt (I := I) x₀)
        (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
        x₀ (X x₀) k l = 0 := by
  classical
  let gInv : M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real :=
    fun y a b => inverseMetricFlatModelInChart_component (I := I) g x₀ a b
      (extChartAt I x₀ y)
  have hinvX : ∀ i j : CoordinateIdx (𝕜 := Real) E,
      (∑ r : CoordinateIdx (𝕜 := Real) E,
        gInv x₀ i r *
          metricCompForMetricInFrame (I := I) g
            (coordinateFrameAt (I := I) x₀) x₀ r j) =
          (if i = j then 1 else 0) ∧
        (∑ r : CoordinateIdx (𝕜 := Real) E,
          metricCompForMetricInFrame (I := I) g
            (coordinateFrameAt (I := I) x₀) x₀ i r * gInv x₀ r j) =
          (if i = j then 1 else 0) := by
    intro i j
    have h := gInvBasisAt (I := I) g x₀ (coordinateFrameAt_mem (I := I) x₀) i j
    simpa [gInv, metricCompForMetricInFrame, coordinateFrameAt_basis_apply] using h
  have hinvN : ∀ i j : CoordinateIdx (𝕜 := Real) E,
      (fun y : M => ∑ r : CoordinateIdx (𝕜 := Real) E,
          gInv y i r *
            metricCompForMetricInFrame (I := I) g
              (coordinateFrameAt (I := I) x₀) y r j) =ᶠ[𝓝 x₀]
        fun _ : M => if i = j then 1 else 0 := by
    intro i j
    simpa [gInv] using gInvBasisNhds (I := I) g x₀ i j
  have hginv_mdiff : ∀ a b : CoordinateIdx (𝕜 := Real) E,
      MDifferentiableAt I 𝓘(Real, Real) (fun y : M => gInv y a b) x₀ := by
    intro a b
    simpa [gInv] using gInvComp_mdiffAt (I := I) g x₀ a b
  have hmetric_mdiff : ∀ a b : CoordinateIdx (𝕜 := Real) E,
      MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M =>
          metricCompForMetricInFrame (I := I) g
            (coordinateFrameAt (I := I) x₀) y a b) x₀ := by
    intro a b
    exact metricComp_mdiffAt (I := I) g
      (coordinateFrameAt (I := I) x₀)
      (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
      (coordinateFrameSet_open (I := I) x₀)
      (coordinateFrameAt_mem (I := I) x₀) a b
  simpa [gInv] using
    invCovZeroLocal (I := I) g gInv cov X
      (coordinateFrameAt (I := I) x₀)
      (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
      hinvX hinvN hmc
      (coordinateFrameSet_open (I := I) x₀)
      (coordinateFrameAt_mem (I := I) x₀)
      hginv_mdiff hmetric_mdiff k l


end Components

end
end DifferentialGeometry.Tensor.Coordinates
