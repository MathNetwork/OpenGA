import DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.F.GeometryFormulaCore


set_option autoImplicit false

namespace DifferentialGeometry.PDE.RicciFlow.Entropy

noncomputable section

open Filter MeasureTheory
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Coordinates
open Tensor0SBundle
open scoped Manifold ContDiff

variable {M : Type*}








section GeometryFormula510

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [InnerProductSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩




omit [InnerProductSpace ℝ E] in
theorem connTraceAction_coord
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SBundle.TensorRSField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 1 2)
    (potential : M -> Real)
    (x₀ : M) {x : M} (hx : x ∈ coordinateFrameSet (I := I) x₀) :
    DifferentialGeometry.Integral.DivergenceTheorem.tangentSectionAction
        (I := I) (DifferentialGeometry.Integral.Connection.connTraceField (I := I) g A)
        potential x =
      ∑ p : CoordinateIdx (𝕜 := Real) E,
        (∑ i : CoordinateIdx (𝕜 := Real) E,
          ∑ j : CoordinateIdx (𝕜 := Real) E,
            inverseMetricFlatModelInChart_component (I := I) g x₀ i j
                (extChartAt I x₀ x) *
              componentRS (I := I) (coordinateFrameAt_basis (I := I) x₀ hx)
                (A x) (fun _ : Fin 1 => p)
                (fun q : Fin 2 => if q = 0 then i else j)) *
          extDerivFun (I := I) potential x
            (coordinateFrameAt (I := I) x₀ p x) := by
  classical
  let X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
    DifferentialGeometry.Integral.Connection.connTraceField (I := I) g A
  let frame := coordinateFrameAt (I := I) x₀
  let hframe := coordinateFrameAt_isLocalFrame (I := I) x₀
  have hX :
      X x = ∑ p : CoordinateIdx (𝕜 := Real) E,
        hframe.coeff p x (X x) • frame p x := by
    simpa [X, frame, hframe] using hframe.coeff_sum_eq (fun y : M => X y) hx
  rw [DifferentialGeometry.Integral.DivergenceTheorem.tangentSectionAction_def]
  rw [← DifferentialGeometry.extDerivFun_real_eq_mfderiv I potential x (X x)]
  change extDerivFun (I := I) potential x (X x) = _
  rw [hX, map_sum]
  refine Finset.sum_congr rfl ?_
  intro p _
  rw [map_smul]
  have hcoeff :=
    DifferentialGeometry.Integral.Connection.connTraceField_coord (I := I) g A x₀ hx p
  rw [hcoeff]
  exact smul_eq_mul ..


def connTraceRawDiv
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SBundle.TensorRSField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 1 2) : M -> Real :=
  fun x =>
    DifferentialGeometry.Integral.DivergenceTheorem.divergence_g
      (I := I) g (DifferentialGeometry.Integral.Connection.connTraceField (I := I) g A) x




def connTraceAction
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SBundle.TensorRSField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 1 2)
    (potential : M -> Real) : M -> Real :=
  fun x =>
    ∑ p : CoordinateIdx (𝕜 := Real) E,
      (∑ i : CoordinateIdx (𝕜 := Real) E,
        ∑ j : CoordinateIdx (𝕜 := Real) E,
          inverseMetricFlatModelInChart_component (I := I) g x i j
              (extChartAt I x x) *
            componentRS (I := I)
              (coordinateFrameAt_basis (I := I) x (coordinateFrameAt_mem (I := I) x))
              (A x) (fun _ : Fin 1 => p)
              (fun q : Fin 2 => if q = 0 then i else j)) *
        extDerivFun (I := I) potential x
          (coordinateFrameAt (I := I) x p x)




def gammaActionTrace
    (g : SmoothRiemannianMetric I M)
    (christoffelVariation :
      M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (gradPotential : M -> CoordinateIdx (𝕜 := Real) E -> Real) :
    M -> Real :=
  fun x =>
    ∑ p : CoordinateIdx (𝕜 := Real) E,
      (∑ i : CoordinateIdx (𝕜 := Real) E,
        ∑ j : CoordinateIdx (𝕜 := Real) E,
          inverseMetricFlatModelInChart_component (I := I) g x i j
              (extChartAt I x x) *
            christoffelVariation x p i j) *
        gradPotential x p



def gammaRawDivergenceTrace
    (g : SmoothRiemannianMetric I M)
    (nablaChristoffelVariation :
      M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real) :
    M -> Real :=
  fun x =>
    ∑ i : CoordinateIdx (𝕜 := Real) E,
      ∑ j : CoordinateIdx (𝕜 := Real) E,
        inverseMetricFlatModelInChart_component (I := I) g x i j
            (extChartAt I x x) *
          (∑ p : CoordinateIdx (𝕜 := Real) E,
            nablaChristoffelVariation x p p i j)

theorem rawDivTraceAlg
    {Idx : Type*} [Fintype Idx]
    (U : Idx -> Idx -> Real)
    (dU : Idx -> Idx -> Idx -> Real)
    (A : Idx -> Idx -> Idx -> Real)
    (dA nablaA : Idx -> Idx -> Idx -> Idx -> Real)
    (Gamma : Idx -> Idx -> Idx -> Real)
    (hUtrace : ∀ d : Idx,
      (∑ i : Idx, ∑ j : Idx, dU d i j * A d i j) =
        -∑ i : Idx, ∑ j : Idx, U i j *
          ((∑ a : Idx, Gamma d i a * A d a j) +
           (∑ a : Idx, Gamma d j a * A d i a)))
    (hAtrace : ∀ i j : Idx,
      (∑ d : Idx, nablaA d d i j) =
        (∑ d : Idx, dA d d i j) +
          (∑ d : Idx, A d i j * (∑ a : Idx, Gamma d a a)) -
          (∑ d : Idx,
            ((∑ a : Idx, Gamma d i a * A d a j) +
             (∑ a : Idx, Gamma d j a * A d i a)))) :
    (∑ d : Idx, ∑ i : Idx, ∑ j : Idx,
        (dU d i j * A d i j + U i j * dA d d i j)) +
      (∑ d : Idx,
        (∑ i : Idx, ∑ j : Idx, U i j * A d i j) *
          (∑ a : Idx, Gamma d a a)) =
      ∑ i : Idx, ∑ j : Idx, U i j * (∑ d : Idx, nablaA d d i j) := by
  classical
  calc
    (∑ d : Idx, ∑ i : Idx, ∑ j : Idx,
        (dU d i j * A d i j + U i j * dA d d i j)) +
      (∑ d : Idx,
        (∑ i : Idx, ∑ j : Idx, U i j * A d i j) *
          (∑ a : Idx, Gamma d a a))
        =
      (∑ d : Idx, ∑ i : Idx, ∑ j : Idx, dU d i j * A d i j) +
      (∑ i : Idx, ∑ j : Idx, U i j *
        (∑ d : Idx, dA d d i j)) +
      (∑ d : Idx,
        (∑ i : Idx, ∑ j : Idx, U i j * A d i j) *
          (∑ a : Idx, Gamma d a a)) := by
          simp only [Finset.sum_add_distrib]
          congr 2
          calc
            (∑ d : Idx, ∑ i : Idx, ∑ j : Idx, U i j * dA d d i j)
                =
              ∑ i : Idx, ∑ j : Idx, ∑ d : Idx, U i j * dA d d i j := by
              calc
                (∑ d : Idx, ∑ i : Idx, ∑ j : Idx, U i j * dA d d i j)
                    =
                  ∑ i : Idx, ∑ d : Idx, ∑ j : Idx, U i j * dA d d i j := by
                  rw [Finset.sum_comm]
                _ =
                  ∑ i : Idx, ∑ j : Idx, ∑ d : Idx, U i j * dA d d i j := by
                  refine Finset.sum_congr rfl fun i _ => ?_
                  rw [Finset.sum_comm]
            _ =
              ∑ i : Idx, ∑ j : Idx, U i j * (∑ d : Idx, dA d d i j) := by
              refine Finset.sum_congr rfl fun i _ => ?_
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [Finset.mul_sum]
    _ =
      (∑ d : Idx,
        -∑ i : Idx, ∑ j : Idx, U i j *
          ((∑ a : Idx, Gamma d i a * A d a j) +
           (∑ a : Idx, Gamma d j a * A d i a))) +
      (∑ i : Idx, ∑ j : Idx, U i j * (∑ d : Idx, dA d d i j)) +
      (∑ d : Idx,
        (∑ i : Idx, ∑ j : Idx, U i j * A d i j) *
          (∑ a : Idx, Gamma d a a)) := by
        rw [show
          (∑ d : Idx, ∑ i : Idx, ∑ j : Idx, dU d i j * A d i j) =
            ∑ d : Idx,
              -∑ i : Idx, ∑ j : Idx, U i j *
                ((∑ a : Idx, Gamma d i a * A d a j) +
                 (∑ a : Idx, Gamma d j a * A d i a)) by
          refine Finset.sum_congr rfl fun d _ => hUtrace d]
     _ =
      ∑ i : Idx, ∑ j : Idx, U i j * (∑ d : Idx, nablaA d d i j) := by
        let L : Idx -> Idx -> Idx -> Real := fun d i j =>
          (∑ a : Idx, Gamma d i a * A d a j) +
            (∑ a : Idx, Gamma d j a * A d i a)
        let T : Idx -> Real := fun d => ∑ a : Idx, Gamma d a a
        have hneg :
            (∑ d : Idx, -∑ i : Idx, ∑ j : Idx, U i j * L d i j) =
              -∑ i : Idx, ∑ j : Idx, U i j * (∑ d : Idx, L d i j) := by
          calc
            (∑ d : Idx, -∑ i : Idx, ∑ j : Idx, U i j * L d i j)
                =
              -∑ d : Idx, ∑ i : Idx, ∑ j : Idx, U i j * L d i j := by
              rw [Finset.sum_neg_distrib]
            _ =
              -∑ i : Idx, ∑ j : Idx, ∑ d : Idx, U i j * L d i j := by
              congr 1
              calc
                (∑ d : Idx, ∑ i : Idx, ∑ j : Idx, U i j * L d i j)
                    =
                  ∑ i : Idx, ∑ d : Idx, ∑ j : Idx, U i j * L d i j := by
                  rw [Finset.sum_comm]
                _ =
                  ∑ i : Idx, ∑ j : Idx, ∑ d : Idx, U i j * L d i j := by
                  refine Finset.sum_congr rfl fun i _ => ?_
                  rw [Finset.sum_comm]
            _ =
              -∑ i : Idx, ∑ j : Idx, U i j * (∑ d : Idx, L d i j) := by
              congr 1
              refine Finset.sum_congr rfl fun i _ => ?_
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [Finset.mul_sum]
        have hden :
            (∑ d : Idx,
              (∑ i : Idx, ∑ j : Idx, U i j * A d i j) * T d) =
              ∑ i : Idx, ∑ j : Idx,
                U i j * (∑ d : Idx, A d i j * T d) := by
          calc
            (∑ d : Idx,
              (∑ i : Idx, ∑ j : Idx, U i j * A d i j) * T d)
                =
              ∑ d : Idx, ∑ i : Idx, ∑ j : Idx,
                U i j * A d i j * T d := by
              refine Finset.sum_congr rfl fun d _ => ?_
              rw [Finset.sum_mul]
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [Finset.sum_mul]
            _ =
              ∑ i : Idx, ∑ j : Idx, ∑ d : Idx,
                U i j * A d i j * T d := by
              calc
                (∑ d : Idx, ∑ i : Idx, ∑ j : Idx,
                  U i j * A d i j * T d)
                    =
                  ∑ i : Idx, ∑ d : Idx, ∑ j : Idx,
                    U i j * A d i j * T d := by
                  rw [Finset.sum_comm]
                _ =
                  ∑ i : Idx, ∑ j : Idx, ∑ d : Idx,
                    U i j * A d i j * T d := by
                  refine Finset.sum_congr rfl fun i _ => ?_
                  rw [Finset.sum_comm]
            _ =
              ∑ i : Idx, ∑ j : Idx,
                U i j * (∑ d : Idx, A d i j * T d) := by
              refine Finset.sum_congr rfl fun i _ => ?_
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun d _ => ?_
              ring
        calc
          (∑ d : Idx, -∑ i : Idx, ∑ j : Idx, U i j *
                ((∑ a : Idx, Gamma d i a * A d a j) +
                 (∑ a : Idx, Gamma d j a * A d i a))) +
              (∑ i : Idx, ∑ j : Idx, U i j * (∑ d : Idx, dA d d i j)) +
            (∑ d : Idx,
              (∑ i : Idx, ∑ j : Idx, U i j * A d i j) *
                (∑ a : Idx, Gamma d a a))
              =
            -∑ i : Idx, ∑ j : Idx, U i j * (∑ d : Idx, L d i j) +
              (∑ i : Idx, ∑ j : Idx, U i j * (∑ d : Idx, dA d d i j)) +
            (∑ i : Idx, ∑ j : Idx,
              U i j * (∑ d : Idx, A d i j * T d)) := by
              simp only [L, T]
              rw [hneg, hden]
          _ =
            ∑ i : Idx, ∑ j : Idx, U i j *
              ((∑ d : Idx, dA d d i j) +
                (∑ d : Idx, A d i j * T d) -
                (∑ d : Idx, L d i j)) := by
              calc
                -∑ i : Idx, ∑ j : Idx, U i j * (∑ d : Idx, L d i j) +
                    (∑ i : Idx, ∑ j : Idx, U i j * (∑ d : Idx, dA d d i j)) +
                  (∑ i : Idx, ∑ j : Idx, U i j * (∑ d : Idx, A d i j * T d))
                    =
                  ∑ i : Idx, ∑ j : Idx,
                    (-(U i j * (∑ d : Idx, L d i j)) +
                      U i j * (∑ d : Idx, dA d d i j) +
                      U i j * (∑ d : Idx, A d i j * T d)) := by
                    simp [Finset.sum_add_distrib, Finset.sum_neg_distrib]
                _ =
                  ∑ i : Idx, ∑ j : Idx, U i j *
                    ((∑ d : Idx, dA d d i j) +
                      (∑ d : Idx, A d i j * T d) -
                      (∑ d : Idx, L d i j)) := by
                    refine Finset.sum_congr rfl fun i _ => ?_
                    refine Finset.sum_congr rfl fun j _ => ?_
                    ring
          _ =
            ∑ i : Idx, ∑ j : Idx, U i j * (∑ d : Idx, nablaA d d i j) := by
              refine Finset.sum_congr rfl fun i _ => ?_
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [hAtrace i j]

private theorem traceUpperAlg
    {Idx : Type*} [Fintype Idx]
    (A : Idx -> Idx -> Idx -> Real)
    (Gamma : Idx -> Idx -> Idx -> Real)
    (hGamma : ∀ d a k : Idx, Gamma d a k = Gamma a d k)
    (i j : Idx) :
    (∑ d : Idx, ∑ a : Idx, Gamma d a d * A a i j) =
      ∑ d : Idx, A d i j * (∑ a : Idx, Gamma d a a) := by
  classical
  calc
    (∑ d : Idx, ∑ a : Idx, Gamma d a d * A a i j)
        =
      ∑ a : Idx, ∑ d : Idx, Gamma d a d * A a i j := by
      rw [Finset.sum_comm]
    _ =
      ∑ a : Idx, ∑ d : Idx, Gamma a d d * A a i j := by
      refine Finset.sum_congr rfl fun a _ => ?_
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [hGamma d a d]
    _ =
      ∑ a : Idx, A a i j * (∑ d : Idx, Gamma a d d) := by
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun d _ => ?_
      ring
    _ =
      ∑ d : Idx, A d i j * (∑ a : Idx, Gamma d a a) := rfl

theorem traceNablaAlg
    {Idx : Type*} [Fintype Idx]
    (A : Idx -> Idx -> Idx -> Real)
    (dA nablaA : Idx -> Idx -> Idx -> Idx -> Real)
    (Gamma : Idx -> Idx -> Idx -> Real)
    (hA : ∀ d k i j : Idx,
      nablaA d k i j =
        dA d k i j +
          (∑ a : Idx, Gamma d a k * A a i j) -
          (∑ a : Idx, Gamma d i a * A k a j) -
          (∑ a : Idx, Gamma d j a * A k i a))
    (hGamma : ∀ d a k : Idx, Gamma d a k = Gamma a d k)
    (i j : Idx) :
    (∑ d : Idx, nablaA d d i j) =
      (∑ d : Idx, dA d d i j) +
        (∑ d : Idx, A d i j * (∑ a : Idx, Gamma d a a)) -
        (∑ d : Idx,
          ((∑ a : Idx, Gamma d i a * A d a j) +
           (∑ a : Idx, Gamma d j a * A d i a))) := by
  classical
  calc
    (∑ d : Idx, nablaA d d i j)
        =
      ∑ d : Idx,
        (dA d d i j +
          (∑ a : Idx, Gamma d a d * A a i j) -
          (∑ a : Idx, Gamma d i a * A d a j) -
          (∑ a : Idx, Gamma d j a * A d i a)) := by
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [hA d d i j]
    _ =
      (∑ d : Idx, dA d d i j) +
        (∑ d : Idx, ∑ a : Idx, Gamma d a d * A a i j) -
        (∑ d : Idx,
          ((∑ a : Idx, Gamma d i a * A d a j) +
           (∑ a : Idx, Gamma d j a * A d i a))) := by
      simp [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      ring
    _ =
      (∑ d : Idx, dA d d i j) +
        (∑ d : Idx, A d i j * (∑ a : Idx, Gamma d a a)) -
        (∑ d : Idx,
          ((∑ a : Idx, Gamma d i a * A d a j) +
           (∑ a : Idx, Gamma d j a * A d i a))) := by
      rw [traceUpperAlg A Gamma hGamma i j]



def christoffelWeightedDivergenceTrace
    (g : SmoothRiemannianMetric I M)
    (nablaChristoffelVariation :
      M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real)
    (christoffelVariation :
      M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (gradPotential : M -> CoordinateIdx (𝕜 := Real) E -> Real) :
    M -> Real :=
  fun x =>
    ∑ i : CoordinateIdx (𝕜 := Real) E,
      ∑ j : CoordinateIdx (𝕜 := Real) E,
        inverseMetricFlatModelInChart_component (I := I) g x i j
            (extChartAt I x x) *
          christoffelWeightedDivergenceInFrame nablaChristoffelVariation
            christoffelVariation gradPotential x i j






omit [InnerProductSpace ℝ E] in
theorem weightedTrace_eq
    (g : SmoothRiemannianMetric I M)
    (nablaChristoffelVariation :
      M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real)
    (christoffelVariation :
      M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (gradPotential : M -> CoordinateIdx (𝕜 := Real) E -> Real) :
    christoffelWeightedDivergenceTrace (I := I) g
        nablaChristoffelVariation christoffelVariation gradPotential =
      fun x =>
        gammaRawDivergenceTrace (I := I) g nablaChristoffelVariation x -
          gammaActionTrace (I := I) g christoffelVariation gradPotential x := by
  classical
  funext x
  unfold christoffelWeightedDivergenceTrace gammaRawDivergenceTrace
    gammaActionTrace christoffelWeightedDivergenceInFrame
  rw [show
      (∑ i : CoordinateIdx (𝕜 := Real) E,
        ∑ j : CoordinateIdx (𝕜 := Real) E,
          inverseMetricFlatModelInChart_component (I := I) g x i j
              (extChartAt I x x) *
            ((∑ p : CoordinateIdx (𝕜 := Real) E,
                nablaChristoffelVariation x p p i j) -
              ∑ p : CoordinateIdx (𝕜 := Real) E,
                christoffelVariation x p i j * gradPotential x p)) =
        (∑ i : CoordinateIdx (𝕜 := Real) E,
          ∑ j : CoordinateIdx (𝕜 := Real) E,
            inverseMetricFlatModelInChart_component (I := I) g x i j
                (extChartAt I x x) *
              (∑ p : CoordinateIdx (𝕜 := Real) E,
                nablaChristoffelVariation x p p i j)) -
          (∑ i : CoordinateIdx (𝕜 := Real) E,
            ∑ j : CoordinateIdx (𝕜 := Real) E,
              inverseMetricFlatModelInChart_component (I := I) g x i j
                  (extChartAt I x x) *
                (∑ p : CoordinateIdx (𝕜 := Real) E,
                  christoffelVariation x p i j * gradPotential x p)) by
      simp only [mul_sub, Finset.sum_sub_distrib]]
  congr 1
  calc
    (∑ i : CoordinateIdx (𝕜 := Real) E,
      ∑ j : CoordinateIdx (𝕜 := Real) E,
        inverseMetricFlatModelInChart_component (I := I) g x i j
            (extChartAt I x x) *
          (∑ p : CoordinateIdx (𝕜 := Real) E,
            christoffelVariation x p i j * gradPotential x p))
        =
      ∑ i : CoordinateIdx (𝕜 := Real) E,
        ∑ j : CoordinateIdx (𝕜 := Real) E,
          ∑ p : CoordinateIdx (𝕜 := Real) E,
            inverseMetricFlatModelInChart_component (I := I) g x i j
                (extChartAt I x x) *
              christoffelVariation x p i j * gradPotential x p := by
        refine Finset.sum_congr rfl fun i _ => ?_
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun p _ => ?_
        ring
    _ =
      ∑ p : CoordinateIdx (𝕜 := Real) E,
        ∑ i : CoordinateIdx (𝕜 := Real) E,
          ∑ j : CoordinateIdx (𝕜 := Real) E,
            inverseMetricFlatModelInChart_component (I := I) g x i j
                (extChartAt I x x) *
              christoffelVariation x p i j * gradPotential x p := by
        calc
          (∑ i : CoordinateIdx (𝕜 := Real) E,
            ∑ j : CoordinateIdx (𝕜 := Real) E,
              ∑ p : CoordinateIdx (𝕜 := Real) E,
                inverseMetricFlatModelInChart_component (I := I) g x i j
                    (extChartAt I x x) *
                  christoffelVariation x p i j * gradPotential x p)
              =
            ∑ i : CoordinateIdx (𝕜 := Real) E,
              ∑ p : CoordinateIdx (𝕜 := Real) E,
                ∑ j : CoordinateIdx (𝕜 := Real) E,
                  inverseMetricFlatModelInChart_component (I := I) g x i j
                      (extChartAt I x x) *
                    christoffelVariation x p i j * gradPotential x p := by
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [Finset.sum_comm]
          _ =
            ∑ p : CoordinateIdx (𝕜 := Real) E,
              ∑ i : CoordinateIdx (𝕜 := Real) E,
                ∑ j : CoordinateIdx (𝕜 := Real) E,
                  inverseMetricFlatModelInChart_component (I := I) g x i j
                      (extChartAt I x x) *
                    christoffelVariation x p i j * gradPotential x p := by
              rw [Finset.sum_comm]
    _ =
      ∑ p : CoordinateIdx (𝕜 := Real) E,
        (∑ i : CoordinateIdx (𝕜 := Real) E,
          ∑ j : CoordinateIdx (𝕜 := Real) E,
            inverseMetricFlatModelInChart_component (I := I) g x i j
                (extChartAt I x x) *
              christoffelVariation x p i j) *
          gradPotential x p := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_mul]



omit [InnerProductSpace ℝ E] in
theorem connTraceAction_eq
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SBundle.TensorRSField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 1 2)
    (potential : M -> Real) (x : M) :
    DifferentialGeometry.Integral.DivergenceTheorem.tangentSectionAction
        (I := I) (DifferentialGeometry.Integral.Connection.connTraceField (I := I) g A)
        potential x =
      connTraceAction (I := I) g A potential x := by
  simpa [connTraceAction] using
    connTraceAction_coord (I := I) g A potential x
      (coordinateFrameAt_mem (I := I) x)





omit [InnerProductSpace ℝ E] in
theorem connTraceAction_eq_gamma
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SBundle.TensorRSField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 1 2)
    (potential : M -> Real)
    (christoffelVariation :
      M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (gradPotential : M -> CoordinateIdx (𝕜 := Real) E -> Real)
    (hA :
      ∀ x : M, ∀ p i j : CoordinateIdx (𝕜 := Real) E,
        componentRS (I := I)
            (coordinateFrameAt_basis (I := I) x (coordinateFrameAt_mem (I := I) x))
            (A x) (fun _ : Fin 1 => p)
            (fun q : Fin 2 => if q = 0 then i else j) =
          christoffelVariation x p i j)
    (hgrad :
      ∀ x : M, ∀ p : CoordinateIdx (𝕜 := Real) E,
        extDerivFun (I := I) potential x (coordinateFrameAt (I := I) x p x) =
          gradPotential x p) :
    connTraceAction (I := I) g A potential =
      gammaActionTrace (I := I) g christoffelVariation gradPotential := by
  funext x
  unfold connTraceAction gammaActionTrace
  refine Finset.sum_congr rfl ?_
  intro p _
  rw [hgrad x p]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro i _
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [hA x p i j]




omit [InnerProductSpace ℝ E] in
theorem weightedTrace_of_raw
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SBundle.TensorRSField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 1 2)
    (potential : M -> Real)
    (nablaChristoffelVariation :
      M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real)
    (christoffelVariation :
      M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (gradPotential : M -> CoordinateIdx (𝕜 := Real) E -> Real)
    (hraw :
      ∀ x : M,
        connTraceRawDiv (I := I) g A x =
          gammaRawDivergenceTrace (I := I) g nablaChristoffelVariation x)
    (hA :
      ∀ x : M, ∀ p i j : CoordinateIdx (𝕜 := Real) E,
        componentRS (I := I)
            (coordinateFrameAt_basis (I := I) x (coordinateFrameAt_mem (I := I) x))
            (A x) (fun _ : Fin 1 => p)
            (fun q : Fin 2 => if q = 0 then i else j) =
          christoffelVariation x p i j)
    (hgrad :
      ∀ x : M, ∀ p : CoordinateIdx (𝕜 := Real) E,
        extDerivFun (I := I) potential x (coordinateFrameAt (I := I) x p x) =
          gradPotential x p) :
    ∀ x : M,
      christoffelWeightedDivergenceTrace (I := I) g
          nablaChristoffelVariation christoffelVariation gradPotential x =
        connTraceRawDiv (I := I) g A x -
          connTraceAction (I := I) g A potential x := by
  intro x
  have hweighted :=
    congrFun
      (weightedTrace_eq (I := I) g nablaChristoffelVariation
        christoffelVariation gradPotential) x
  have haction :=
    congrFun
      (connTraceAction_eq_gamma (I := I) g A potential
        christoffelVariation gradPotential hA hgrad) x
  calc
    christoffelWeightedDivergenceTrace (I := I) g
        nablaChristoffelVariation christoffelVariation gradPotential x =
      gammaRawDivergenceTrace (I := I) g nablaChristoffelVariation x -
        gammaActionTrace (I := I) g christoffelVariation gradPotential x := hweighted
    _ = connTraceRawDiv (I := I) g A x -
          connTraceAction (I := I) g A potential x := by
        rw [← hraw x, ← haction]


end GeometryFormula510

end

end DifferentialGeometry.PDE.RicciFlow.Entropy
