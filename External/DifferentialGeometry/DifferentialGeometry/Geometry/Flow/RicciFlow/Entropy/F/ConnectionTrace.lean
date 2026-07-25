import DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.F.ChartTrace


set_option autoImplicit false

namespace DifferentialGeometry.PDE.RicciFlow.Entropy

noncomputable section

open Filter MeasureTheory
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Tensor.Coordinates
open Tensor0SBundle
open scoped Manifold ContDiff

variable {M : Type*}


















section GeometryFormula510

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete Real E

set_option maxHeartbeats 1600000 in



omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [T2Space M] [SigmaCompactSpace M] in
theorem connTraceUTrace
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SBundle.TensorRSField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 1 2)
    (gInvDeriv :
      CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (x : M)
    (hginvDeriv :
      ∀ d i j : CoordinateIdx (𝕜 := Real) E,
        gInvDeriv d i j =
          extDerivFun (I := I)
            (fun y : M =>
              inverseMetricFlatModelInChart_component (I := I) g x i j
                (extChartAt I x y))
            x (coordinateFrameAt (I := I) x d x))
    (hzero :
      ∀ d i j : CoordinateIdx (𝕜 := Real) E,
        inverseMetricCovDerivForMetricCompInFrame
          (I := I)
          (fun y : M => fun a b : CoordinateIdx (𝕜 := Real) E =>
            inverseMetricFlatModelInChart_component (I := I) g x a b
              (extChartAt I x y))
          cov (coordinateFrameAt (I := I) x)
          (coordinateFrameAt_isLocalFrame_one (I := I) x)
          x d i j = 0) :
    ∀ d : CoordinateIdx (𝕜 := Real) E,
      (∑ i : CoordinateIdx (𝕜 := Real) E,
        ∑ j : CoordinateIdx (𝕜 := Real) E,
          gInvDeriv d i j *
            componentRS (I := I)
              (coordinateFrameAt_basis (I := I) x
                (coordinateFrameAt_mem (I := I) x))
              (A x) (fun _ : Fin 1 => d)
              (fun q : Fin 2 => if q = 0 then i else j)) =
        -∑ i : CoordinateIdx (𝕜 := Real) E,
          ∑ j : CoordinateIdx (𝕜 := Real) E,
            inverseMetricFlatModelInChart_component (I := I) g x i j
                (extChartAt I x x) *
              ((∑ a : CoordinateIdx (𝕜 := Real) E,
                christoffelSymbolInFrame cov
                  (coordinateFrameAt (I := I) x)
                  (coordinateFrameAt_isLocalFrame_one (I := I) x) x d i a *
                  componentRS (I := I)
                    (coordinateFrameAt_basis (I := I) x
                      (coordinateFrameAt_mem (I := I) x))
                    (A x) (fun _ : Fin 1 => d)
                    (fun q : Fin 2 => if q = 0 then a else j)) +
               (∑ a : CoordinateIdx (𝕜 := Real) E,
                christoffelSymbolInFrame cov
                  (coordinateFrameAt (I := I) x)
                  (coordinateFrameAt_isLocalFrame_one (I := I) x) x d j a *
                  componentRS (I := I)
                    (coordinateFrameAt_basis (I := I) x
                      (coordinateFrameAt_mem (I := I) x))
                    (A x) (fun _ : Fin 1 => d)
                    (fun q : Fin 2 => if q = 0 then i else a))) := by
  classical
  intro d
  let Acomp : CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real :=
    fun i j =>
      componentRS (I := I)
        (coordinateFrameAt_basis (I := I) x (coordinateFrameAt_mem (I := I) x))
        (A x) (fun _ : Fin 1 => d) (fun q : Fin 2 => if q = 0 then i else j)
  have hcancel :=
    DifferentialGeometry.Integral.Connection.gInvTraceCancel
      (I := I)
      (gInv := fun y : M => fun a b : CoordinateIdx (𝕜 := Real) E =>
        inverseMetricFlatModelInChart_component (I := I) g x a b
          (extChartAt I x y))
      (metricDot := fun _ : M => Acomp)
      (cov := cov)
      (frame := coordinateFrameAt (I := I) x)
      (hframe := coordinateFrameAt_isLocalFrame_one (I := I) x)
      (x := x) (d := d) (hzero d)
  calc
    (∑ i : CoordinateIdx (𝕜 := Real) E,
      ∑ j : CoordinateIdx (𝕜 := Real) E,
        gInvDeriv d i j *
          componentRS (I := I)
            (coordinateFrameAt_basis (I := I) x
              (coordinateFrameAt_mem (I := I) x))
            (A x) (fun _ : Fin 1 => d)
            (fun q : Fin 2 => if q = 0 then i else j))
        =
      ∑ i : CoordinateIdx (𝕜 := Real) E,
        ∑ j : CoordinateIdx (𝕜 := Real) E,
          extDerivFun (I := I)
              (fun y : M =>
                inverseMetricFlatModelInChart_component (I := I) g x i j
                  (extChartAt I x y))
              x (coordinateFrameAt (I := I) x d x) *
            Acomp i j := by
        refine Finset.sum_congr rfl fun i _ => ?_
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hginvDeriv d i j]
    _ =
      -∑ i : CoordinateIdx (𝕜 := Real) E,
        ∑ j : CoordinateIdx (𝕜 := Real) E,
          inverseMetricFlatModelInChart_component (I := I) g x i j
              (extChartAt I x x) *
            ((∑ a : CoordinateIdx (𝕜 := Real) E,
              christoffelSymbolInFrame cov
                (coordinateFrameAt (I := I) x)
                (coordinateFrameAt_isLocalFrame_one (I := I) x) x d i a *
                Acomp a j) +
             (∑ a : CoordinateIdx (𝕜 := Real) E,
              christoffelSymbolInFrame cov
                (coordinateFrameAt (I := I) x)
                (coordinateFrameAt_isLocalFrame_one (I := I) x) x d j a *
                Acomp i a)) := by
        simpa [Acomp] using hcancel
    _ =
      -∑ i : CoordinateIdx (𝕜 := Real) E,
        ∑ j : CoordinateIdx (𝕜 := Real) E,
          inverseMetricFlatModelInChart_component (I := I) g x i j
              (extChartAt I x x) *
            ((∑ a : CoordinateIdx (𝕜 := Real) E,
              christoffelSymbolInFrame cov
                (coordinateFrameAt (I := I) x)
                (coordinateFrameAt_isLocalFrame_one (I := I) x) x d i a *
                componentRS (I := I)
                  (coordinateFrameAt_basis (I := I) x
                    (coordinateFrameAt_mem (I := I) x))
                  (A x) (fun _ : Fin 1 => d)
                  (fun q : Fin 2 => if q = 0 then a else j)) +
             (∑ a : CoordinateIdx (𝕜 := Real) E,
              christoffelSymbolInFrame cov
                (coordinateFrameAt (I := I) x)
                (coordinateFrameAt_isLocalFrame_one (I := I) x) x d j a *
                componentRS (I := I)
                  (coordinateFrameAt_basis (I := I) x
                    (coordinateFrameAt_mem (I := I) x))
                  (A x) (fun _ : Fin 1 => d)
                  (fun q : Fin 2 => if q = 0 then i else a))) := rfl

set_option maxHeartbeats 1600000 in


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem connTraceATrace
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    (A : Tensor0SBundle.TensorRSField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 1 2)
    (nablaChristoffelVariation :
      M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real)
    (componentDeriv :
      CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real)
    (x : M)
    (hNabla : ∀ d k i j : CoordinateIdx (𝕜 := Real) E,
      nablaChristoffelVariation x d k i j =
        componentDeriv d k i j +
          (∑ a : CoordinateIdx (𝕜 := Real) E,
            christoffelSymbolInFrame cov
              (coordinateFrameAt (I := I) x)
              (coordinateFrameAt_isLocalFrame_one (I := I) x) x d a k *
              componentRS (I := I)
                (coordinateFrameAt_basis (I := I) x
                  (coordinateFrameAt_mem (I := I) x))
                (A x) (fun _ : Fin 1 => a)
                (fun q : Fin 2 => if q = 0 then i else j)) -
          (∑ a : CoordinateIdx (𝕜 := Real) E,
            christoffelSymbolInFrame cov
              (coordinateFrameAt (I := I) x)
              (coordinateFrameAt_isLocalFrame_one (I := I) x) x d i a *
              componentRS (I := I)
                (coordinateFrameAt_basis (I := I) x
                  (coordinateFrameAt_mem (I := I) x))
                (A x) (fun _ : Fin 1 => k)
                (fun q : Fin 2 => if q = 0 then a else j)) -
          (∑ a : CoordinateIdx (𝕜 := Real) E,
            christoffelSymbolInFrame cov
              (coordinateFrameAt (I := I) x)
              (coordinateFrameAt_isLocalFrame_one (I := I) x) x d j a *
              componentRS (I := I)
                (coordinateFrameAt_basis (I := I) x
                  (coordinateFrameAt_mem (I := I) x))
                (A x) (fun _ : Fin 1 => k)
                (fun q : Fin 2 => if q = 0 then i else a)))
    (hGamma : ∀ d a k : CoordinateIdx (𝕜 := Real) E,
      christoffelSymbolInFrame cov
        (coordinateFrameAt (I := I) x)
        (coordinateFrameAt_isLocalFrame_one (I := I) x) x d a k =
      christoffelSymbolInFrame cov
        (coordinateFrameAt (I := I) x)
        (coordinateFrameAt_isLocalFrame_one (I := I) x) x a d k) :
    ∀ i j : CoordinateIdx (𝕜 := Real) E,
      (∑ d : CoordinateIdx (𝕜 := Real) E,
        nablaChristoffelVariation x d d i j) =
        (∑ d : CoordinateIdx (𝕜 := Real) E, componentDeriv d d i j) +
          (∑ d : CoordinateIdx (𝕜 := Real) E,
            componentRS (I := I)
              (coordinateFrameAt_basis (I := I) x
                (coordinateFrameAt_mem (I := I) x))
              (A x) (fun _ : Fin 1 => d)
              (fun q : Fin 2 => if q = 0 then i else j) *
              (∑ a : CoordinateIdx (𝕜 := Real) E,
                christoffelSymbolInFrame cov
                  (coordinateFrameAt (I := I) x)
                  (coordinateFrameAt_isLocalFrame_one (I := I) x) x d a a)) -
          (∑ d : CoordinateIdx (𝕜 := Real) E,
            ((∑ a : CoordinateIdx (𝕜 := Real) E,
              christoffelSymbolInFrame cov
                (coordinateFrameAt (I := I) x)
                (coordinateFrameAt_isLocalFrame_one (I := I) x) x d i a *
                componentRS (I := I)
                  (coordinateFrameAt_basis (I := I) x
                    (coordinateFrameAt_mem (I := I) x))
                  (A x) (fun _ : Fin 1 => d)
                  (fun q : Fin 2 => if q = 0 then a else j)) +
             (∑ a : CoordinateIdx (𝕜 := Real) E,
              christoffelSymbolInFrame cov
                (coordinateFrameAt (I := I) x)
                (coordinateFrameAt_isLocalFrame_one (I := I) x) x d j a *
                componentRS (I := I)
                  (coordinateFrameAt_basis (I := I) x
                    (coordinateFrameAt_mem (I := I) x))
                  (A x) (fun _ : Fin 1 => d)
                  (fun q : Fin 2 => if q = 0 then i else a)))) := by
  classical
  intro i j
  let Acomp :
      CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real := fun p i j =>
    componentRS (I := I)
      (coordinateFrameAt_basis (I := I) x (coordinateFrameAt_mem (I := I) x))
      (A x) (fun _ : Fin 1 => p) (fun q : Fin 2 => if q = 0 then i else j)
  let Gamma :
      CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real := fun d a k =>
    christoffelSymbolInFrame cov
      (coordinateFrameAt (I := I) x)
      (coordinateFrameAt_isLocalFrame_one (I := I) x) x d a k
  have h :=
    traceNablaAlg (A := Acomp) (dA := componentDeriv)
      (nablaA := fun d k i j => nablaChristoffelVariation x d k i j)
      (Gamma := Gamma)
      (by simpa [Acomp, Gamma] using hNabla)
      (by simpa [Gamma] using hGamma)
      i j
  simpa [Acomp, Gamma] using h

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private theorem gInvFun_mdifferentiableAt
    (g : SmoothRiemannianMetric I M)
    (x : M) (i j : CoordinateIdx (𝕜 := Real) E) :
    MDifferentiableAt I 𝓘(Real, Real) (gInvFun (I := I) g x i j) x :=
  (gInvComp_contMDiffAt (I := I) g x i j).mdifferentiableAt (by norm_num)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private theorem compFun_mdifferentiableAt
    (A : Tensor0SBundle.TensorRSField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 1 2)
    (x : M) (p i j : CoordinateIdx (𝕜 := Real) E) :
    MDifferentiableAt I 𝓘(Real, Real) (compFun (I := I) A x p i j) x :=
  (tensorRS_eval_constInChart_coordinateFrame_contMDiffAt
    (𝕜 := Real) (I := I) (M := M) A x
    (fun _ : Fin 1 => p)
    (fun q : Fin 2 => if q = 0 then i else j)).mdifferentiableAt (by norm_num)



omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private theorem compFun_center
    (A : Tensor0SBundle.TensorRSField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 1 2)
    (x : M) (p i j : CoordinateIdx (𝕜 := Real) E) :
    compFun (I := I) A x p i j x =
      componentRS (I := I)
        (coordinateFrameAt_basis (I := I) x (coordinateFrameAt_mem (I := I) x))
        (A x) (fun _ : Fin 1 => p)
        (fun q : Fin 2 => if q = 0 then i else j) := by
  classical
  haveI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
    change IsManifold I ∞ M
    infer_instance
  have hconst :
      Tensor0SSpace.constInChart (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) 1 x
          ((continuousMultilinearMap_basis
            (𝕜 := Real) (F := E) (Module.finBasis Real E) 1)
            (fun _ : Fin 1 => p)) x =
        basisTensor0S (I := I)
          (coordinateFrameAt_basis (I := I) x (coordinateFrameAt_mem (I := I) x))
          (fun _ : Fin 1 => p) :=
    DifferentialGeometry.Tensor.Coordinates.constInChart_basisTensor0S_coordFrame
      (𝕜 := Real) (I := I) (M := M) (r := 1) x (coordinateFrameAt_mem (I := I) x)
      (fun _ : Fin 1 => p)
  rw [compFun]
  rw [componentRS]
  simp [hconst, component0S, coordinateFrameAt_basis_apply]


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private theorem gInvFun_center
    (g : SmoothRiemannianMetric I M)
    (x : M) (i j : CoordinateIdx (𝕜 := Real) E) :
    gInvFun (I := I) g x i j x =
      inverseMetricFlatModelInChart_component (I := I) g x i j (extChartAt I x x) := rfl



omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private theorem connTraceCoeff_one_center
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SBundle.TensorRSField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 1 2)
    (x : M) (p : CoordinateIdx (𝕜 := Real) E) :
    (coordinateFrameAt_isLocalFrame_one (I := I) x).coeff p x
        ((DifferentialGeometry.Integral.Connection.connTraceField (I := I) g A).toFun x) =
      ∑ i : CoordinateIdx (𝕜 := Real) E,
        ∑ j : CoordinateIdx (𝕜 := Real) E,
          gInvFun (I := I) g x i j x * compFun (I := I) A x p i j x := by
  classical
  have hev := connTraceCoeff_one_eventually (I := I) g A x p
  exact hev.eq_of_nhds

set_option maxHeartbeats 1600000 in







omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private theorem connTraceRawDiv_eq_productSum
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SBundle.TensorRSField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 1 2)
    (x : M)
    (hcov : cov = DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g)
    (hGamma : ∀ d a k : CoordinateIdx (𝕜 := Real) E,
      christoffelSymbolInFrame cov
        (coordinateFrameAt (I := I) x)
        (coordinateFrameAt_isLocalFrame_one (I := I) x) x d a k =
      christoffelSymbolInFrame cov
        (coordinateFrameAt (I := I) x)
        (coordinateFrameAt_isLocalFrame_one (I := I) x) x a d k) :
    connTraceRawDiv (I := I) g A x =
      (∑ p : CoordinateIdx (𝕜 := Real) E,
        ∑ i : CoordinateIdx (𝕜 := Real) E,
          ∑ j : CoordinateIdx (𝕜 := Real) E,
            (extDerivFun (I := I) (gInvFun (I := I) g x i j) x
                  (coordinateFrameAt (I := I) x p x) *
                compFun (I := I) A x p i j x +
              gInvFun (I := I) g x i j x *
                extDerivFun (I := I) (compFun (I := I) A x p i j) x
                  (coordinateFrameAt (I := I) x p x))) +
        (∑ p : CoordinateIdx (𝕜 := Real) E,
          (∑ i : CoordinateIdx (𝕜 := Real) E,
            ∑ j : CoordinateIdx (𝕜 := Real) E,
              gInvFun (I := I) g x i j x * compFun (I := I) A x p i j x) *
            (∑ a : CoordinateIdx (𝕜 := Real) E,
              christoffelSymbolInFrame cov
                (coordinateFrameAt (I := I) x)
                (coordinateFrameAt_isLocalFrame_one (I := I) x) x p a a)) := by
  classical
  set Z := DifferentialGeometry.Integral.Connection.connTraceField (I := I) g A with hZ

  have hbridge :=
    DifferentialGeometry.Integral.Connection.divergence_g_eq_coordinateFrame_covariant_divergence
      (I := I) g Z x
  have hrawdef :
      connTraceRawDiv (I := I) g A x =
        DifferentialGeometry.Integral.DivergenceTheorem.divergence_g (I := I) g Z x := rfl
  rw [hrawdef, hbridge]

  subst hcov

  rw [Finset.sum_add_distrib]
  congr 1
  ·

    refine Finset.sum_congr rfl fun p _ => ?_
    have hev' :
        (fun y : M =>
            (coordinateFrameAt_isLocalFrame_one (I := I) x).coeff p y (Z.toFun y))
          =ᶠ[nhds x]
          fun y : M =>
            ∑ i : CoordinateIdx (𝕜 := Real) E,
              ∑ j : CoordinateIdx (𝕜 := Real) E,
                gInvFun (I := I) g x i j y * compFun (I := I) A x p i j y := by
      rw [hZ]
      exact connTraceCoeff_one_eventually (I := I) g A x p
    have hderiv_eq :
        extDerivFun (I := I)
            (fun y : M =>
              (coordinateFrameAt_isLocalFrame_one (I := I) x).coeff p y (Z.toFun y))
            x (coordinateFrameAt (I := I) x p x) =
          extDerivFun (I := I)
            (fun y : M =>
              ∑ i : CoordinateIdx (𝕜 := Real) E,
                ∑ j : CoordinateIdx (𝕜 := Real) E,
                  gInvFun (I := I) g x i j y * compFun (I := I) A x p i j y)
            x (coordinateFrameAt (I := I) x p x) := by
      rw [extDerivFun_real_eq_mfderiv, extDerivFun_real_eq_mfderiv]
      congr 1
      exact Filter.EventuallyEq.mfderiv_eq hev'
    rw [hderiv_eq]
    rw [extDerivFun_finset_sum_sum_mul_at (I := I) Finset.univ Finset.univ
      (fun i j => gInvFun (I := I) g x i j)
      (fun i j => compFun (I := I) A x p i j)
      (coordinateFrameAt (I := I) x p x)
      (fun i _ j _ => gInvFun_mdifferentiableAt (I := I) g x i j)
      (fun i _ j _ => compFun_mdifferentiableAt (I := I) A x p i j)]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  ·


    have hcoeff_l : ∀ l : CoordinateIdx (𝕜 := Real) E,
        (coordinateFrameAt_isLocalFrame_one (I := I) x).coeff l x (Z.toFun x) =
          ∑ i : CoordinateIdx (𝕜 := Real) E,
            ∑ j : CoordinateIdx (𝕜 := Real) E,
              gInvFun (I := I) g x i j x * compFun (I := I) A x l i j x := by
      intro l
      exact connTraceCoeff_one_center (I := I) g A x l

    calc
      (∑ p : CoordinateIdx (𝕜 := Real) E,
        ∑ l : CoordinateIdx (𝕜 := Real) E,
          christoffelSymbolInFrame (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g)
              (coordinateFrameAt (I := I) x)
              (coordinateFrameAt_isLocalFrame_one (I := I) x) x p l p *
            (coordinateFrameAt_isLocalFrame_one (I := I) x).coeff l x (Z.toFun x))
          =
        ∑ l : CoordinateIdx (𝕜 := Real) E,
          (∑ p : CoordinateIdx (𝕜 := Real) E,
            christoffelSymbolInFrame (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g)
              (coordinateFrameAt (I := I) x)
              (coordinateFrameAt_isLocalFrame_one (I := I) x) x p l p) *
            (∑ i : CoordinateIdx (𝕜 := Real) E,
              ∑ j : CoordinateIdx (𝕜 := Real) E,
                gInvFun (I := I) g x i j x * compFun (I := I) A x l i j x) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [hcoeff_l l]
      _ =
        ∑ p : CoordinateIdx (𝕜 := Real) E,
          (∑ i : CoordinateIdx (𝕜 := Real) E,
            ∑ j : CoordinateIdx (𝕜 := Real) E,
              gInvFun (I := I) g x i j x * compFun (I := I) A x p i j x) *
            (∑ a : CoordinateIdx (𝕜 := Real) E,
              christoffelSymbolInFrame (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g)
                (coordinateFrameAt (I := I) x)
                (coordinateFrameAt_isLocalFrame_one (I := I) x) x p a a) := by
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [mul_comm]
          congr 1
          refine Finset.sum_congr rfl fun p _ => ?_
          exact hGamma p l p

set_option maxHeartbeats 1600000 in









omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem connTraceRaw_eq_gamma
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    (g : SmoothRiemannianMetric I M)
    (hcov : cov = DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g)
    (A : Tensor0SBundle.TensorRSField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 1 2)
    (nablaChristoffelVariation :
      M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real)
    (x : M)
    (hzero :
      ∀ d i j : CoordinateIdx (𝕜 := Real) E,
        inverseMetricCovDerivForMetricCompInFrame
          (I := I)
          (fun y : M => fun a b : CoordinateIdx (𝕜 := Real) E =>
            inverseMetricFlatModelInChart_component (I := I) g x a b
              (extChartAt I x y))
          cov (coordinateFrameAt (I := I) x)
          (coordinateFrameAt_isLocalFrame_one (I := I) x)
          x d i j = 0)
    (hNabla : ∀ d k i j : CoordinateIdx (𝕜 := Real) E,
      nablaChristoffelVariation x d k i j =
        extDerivFun (I := I) (compFun (I := I) A x k i j) x
            (coordinateFrameAt (I := I) x d x) +
          (∑ a : CoordinateIdx (𝕜 := Real) E,
            christoffelSymbolInFrame cov
              (coordinateFrameAt (I := I) x)
              (coordinateFrameAt_isLocalFrame_one (I := I) x) x d a k *
              componentRS (I := I)
                (coordinateFrameAt_basis (I := I) x
                  (coordinateFrameAt_mem (I := I) x))
                (A x) (fun _ : Fin 1 => a)
                (fun q : Fin 2 => if q = 0 then i else j)) -
          (∑ a : CoordinateIdx (𝕜 := Real) E,
            christoffelSymbolInFrame cov
              (coordinateFrameAt (I := I) x)
              (coordinateFrameAt_isLocalFrame_one (I := I) x) x d i a *
              componentRS (I := I)
                (coordinateFrameAt_basis (I := I) x
                  (coordinateFrameAt_mem (I := I) x))
                (A x) (fun _ : Fin 1 => k)
                (fun q : Fin 2 => if q = 0 then a else j)) -
          (∑ a : CoordinateIdx (𝕜 := Real) E,
            christoffelSymbolInFrame cov
              (coordinateFrameAt (I := I) x)
              (coordinateFrameAt_isLocalFrame_one (I := I) x) x d j a *
              componentRS (I := I)
                (coordinateFrameAt_basis (I := I) x
                  (coordinateFrameAt_mem (I := I) x))
                (A x) (fun _ : Fin 1 => k)
                (fun q : Fin 2 => if q = 0 then i else a)))
    (hGamma : ∀ d a k : CoordinateIdx (𝕜 := Real) E,
      christoffelSymbolInFrame cov
        (coordinateFrameAt (I := I) x)
        (coordinateFrameAt_isLocalFrame_one (I := I) x) x d a k =
      christoffelSymbolInFrame cov
        (coordinateFrameAt (I := I) x)
        (coordinateFrameAt_isLocalFrame_one (I := I) x) x a d k) :
    connTraceRawDiv (I := I) g A x =
      gammaRawDivergenceTrace (I := I) g nablaChristoffelVariation x := by
  classical

  set dU : CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
      CoordinateIdx (𝕜 := Real) E -> Real :=
    fun d i j =>
      extDerivFun (I := I) (gInvFun (I := I) g x i j) x
        (coordinateFrameAt (I := I) x d x) with hdU
  set dA : CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
      CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real :=
    fun d k i j =>
      extDerivFun (I := I) (compFun (I := I) A x k i j) x
        (coordinateFrameAt (I := I) x d x) with hdA
  set U : CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real :=
    fun i j => gInvFun (I := I) g x i j x with hU
  set Acomp : CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
      CoordinateIdx (𝕜 := Real) E -> Real :=
    fun p i j =>
      componentRS (I := I)
        (coordinateFrameAt_basis (I := I) x (coordinateFrameAt_mem (I := I) x))
        (A x) (fun _ : Fin 1 => p) (fun q : Fin 2 => if q = 0 then i else j)
    with hAcomp
  set Gamma : CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
      CoordinateIdx (𝕜 := Real) E -> Real :=
    fun d a c =>
      christoffelSymbolInFrame cov
        (coordinateFrameAt (I := I) x)
        (coordinateFrameAt_isLocalFrame_one (I := I) x) x d a c with hGammaDef

  have hUtrace :=
    connTraceUTrace (I := I) (cov := cov) g A dU x (fun d i j => rfl) hzero

  have hAtrace :=
    connTraceATrace (I := I) (cov := cov) A nablaChristoffelVariation
      (fun d k i j => dA d k i j) x hNabla hGamma

  have hprod := connTraceRawDiv_eq_productSum (I := I) (cov := cov) g A x hcov hGamma

  have hraw := rawDivTraceAlg
    (U := U) (dU := dU) (A := Acomp) (dA := dA)
    (nablaA := fun d k i j => nablaChristoffelVariation x d k i j)
    (Gamma := Gamma)
    (by
      intro d
      have h := hUtrace d
      simpa [U, Acomp, Gamma, compFun_center] using h)
    (by
      intro i j
      have h := hAtrace i j
      simpa [Acomp, Gamma] using h)

  rw [hprod]
  rw [show
      (∑ p : CoordinateIdx (𝕜 := Real) E,
        ∑ i : CoordinateIdx (𝕜 := Real) E,
          ∑ j : CoordinateIdx (𝕜 := Real) E,
            (extDerivFun (I := I) (gInvFun (I := I) g x i j) x
                  (coordinateFrameAt (I := I) x p x) *
                compFun (I := I) A x p i j x +
              gInvFun (I := I) g x i j x *
                extDerivFun (I := I) (compFun (I := I) A x p i j) x
                  (coordinateFrameAt (I := I) x p x))) +
        (∑ p : CoordinateIdx (𝕜 := Real) E,
          (∑ i : CoordinateIdx (𝕜 := Real) E,
            ∑ j : CoordinateIdx (𝕜 := Real) E,
              gInvFun (I := I) g x i j x * compFun (I := I) A x p i j x) *
            (∑ a : CoordinateIdx (𝕜 := Real) E,
              christoffelSymbolInFrame cov
                (coordinateFrameAt (I := I) x)
                (coordinateFrameAt_isLocalFrame_one (I := I) x) x p a a)) =
        (∑ d : CoordinateIdx (𝕜 := Real) E,
          ∑ i : CoordinateIdx (𝕜 := Real) E,
            ∑ j : CoordinateIdx (𝕜 := Real) E,
              (dU d i j * Acomp d i j + U i j * dA d d i j)) +
          (∑ d : CoordinateIdx (𝕜 := Real) E,
            (∑ i : CoordinateIdx (𝕜 := Real) E,
              ∑ j : CoordinateIdx (𝕜 := Real) E, U i j * Acomp d i j) *
              (∑ a : CoordinateIdx (𝕜 := Real) E, Gamma d a a)) from by
      simp only [hdU, hdA, hU, hAcomp, hGammaDef, compFun_center]]
  rw [hraw]

  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hU]
  rfl





omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem connTraceRaw_of_components
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    (g : SmoothRiemannianMetric I M)
    (hcov : cov = DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g)
    (A : Tensor0SBundle.TensorRSField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 1 2)
    (nablaChristoffelVariation :
      M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real)
    (hzero : ∀ x : M, ∀ d i j : CoordinateIdx (𝕜 := Real) E,
      inverseMetricCovDerivForMetricCompInFrame
        (I := I)
        (fun y : M => fun a b : CoordinateIdx (𝕜 := Real) E =>
          inverseMetricFlatModelInChart_component (I := I) g x a b
            (extChartAt I x y))
        cov (coordinateFrameAt (I := I) x)
        (coordinateFrameAt_isLocalFrame_one (I := I) x)
        x d i j = 0)
    (hNabla : ∀ x : M, ∀ d k i j : CoordinateIdx (𝕜 := Real) E,
      nablaChristoffelVariation x d k i j =
        extDerivFun (I := I) (compFun (I := I) A x k i j) x
            (coordinateFrameAt (I := I) x d x) +
          (∑ a : CoordinateIdx (𝕜 := Real) E,
            christoffelSymbolInFrame cov
              (coordinateFrameAt (I := I) x)
              (coordinateFrameAt_isLocalFrame_one (I := I) x) x d a k *
              componentRS (I := I)
                (coordinateFrameAt_basis (I := I) x
                  (coordinateFrameAt_mem (I := I) x))
                (A x) (fun _ : Fin 1 => a)
                (fun q : Fin 2 => if q = 0 then i else j)) -
          (∑ a : CoordinateIdx (𝕜 := Real) E,
            christoffelSymbolInFrame cov
              (coordinateFrameAt (I := I) x)
              (coordinateFrameAt_isLocalFrame_one (I := I) x) x d i a *
              componentRS (I := I)
                (coordinateFrameAt_basis (I := I) x
                  (coordinateFrameAt_mem (I := I) x))
                (A x) (fun _ : Fin 1 => k)
                (fun q : Fin 2 => if q = 0 then a else j)) -
          (∑ a : CoordinateIdx (𝕜 := Real) E,
            christoffelSymbolInFrame cov
              (coordinateFrameAt (I := I) x)
              (coordinateFrameAt_isLocalFrame_one (I := I) x) x d j a *
              componentRS (I := I)
                (coordinateFrameAt_basis (I := I) x
                  (coordinateFrameAt_mem (I := I) x))
                (A x) (fun _ : Fin 1 => k)
                (fun q : Fin 2 => if q = 0 then i else a)))
    (hGamma : ∀ x : M, ∀ d a k : CoordinateIdx (𝕜 := Real) E,
      christoffelSymbolInFrame cov
        (coordinateFrameAt (I := I) x)
        (coordinateFrameAt_isLocalFrame_one (I := I) x) x d a k =
      christoffelSymbolInFrame cov
        (coordinateFrameAt (I := I) x)
        (coordinateFrameAt_isLocalFrame_one (I := I) x) x a d k) :
    ∀ x : M,
      connTraceRawDiv (I := I) g A x =
        gammaRawDivergenceTrace (I := I) g nablaChristoffelVariation x := by
  intro x
  exact connTraceRaw_eq_gamma (I := I) (cov := cov) g hcov A
    nablaChristoffelVariation x (hzero x) (hNabla x) (hGamma x)

end GeometryFormula510

end

end DifferentialGeometry.PDE.RicciFlow.Entropy
