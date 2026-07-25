import DifferentialGeometry.Geometry.Curvature.Bochner.ScalarBochner
import DifferentialGeometry.Geometry.Curvature.Realized.CurvatureTensor
import DifferentialGeometry.Geometry.Coordinates.MetricCompatibility.Inverse
import DifferentialGeometry.Geometry.Coordinates.MetricCompatibility.Covariant
import DifferentialGeometry.Geometry.Coordinates.MetricCompatibility.Coordinate
import DifferentialGeometry.Geometry.Coordinates.Tensor
import DifferentialGeometry.Tensor.RSTensor.Tensor0SRiemannian.Basic
import DifferentialGeometry.Tensor.RSTensor.Tensor0SRiemannian.Coordinate
import DifferentialGeometry.Tensor.RSTensor.Tensor0SRiemannian.Comparison
import DifferentialGeometry.Tensor.RSTensor.Tensor0SRiemannian.Product
import DifferentialGeometry.Tensor.RSTensor.Tensor0SRiemannian.Smooth
import DifferentialGeometry.Tensor.Multilinear.BundleSmoothEvalRealized
set_option autoImplicit false
set_option linter.style.longLine false
set_option backward.isDefEq.respectTransparency false













namespace DifferentialGeometry.Integral.Connection

noncomputable section

open Bundle Tensor0SBundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {Time : Type*}



section TensorInner

variable [FiniteDimensional Real E]



abbrev Tensor02Field (Time : Type*) :=
  Time -> Tensor02Section (I := I) (M := M)



def InverseMetricComponentsInFrameTime
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (G : RealizedMetricFamily (I := I) (M := M) Time)
    (gInv : Time -> InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) : Prop :=
  forall t x i j,
    (∑ k : Idx, gInv t x i k * (G.metric t).inner x (frame k x) (frame j x)) =
        (if i = j then 1 else 0) ∧
      (∑ k : Idx, (G.metric t).inner x (frame i x) (frame k x) * gInv t x k j) =
        (if i = j then 1 else 0)

private noncomputable instance tangentSpace_addCommMonoid (x : M) :
    AddCommMonoid (TangentSpace I x) :=
  inferInstanceAs (AddCommMonoid E)

private noncomputable instance tangentSpace_module (x : M) :
    Module Real (TangentSpace I x) :=
  inferInstanceAs (Module Real E)



def inner02
    (g : SmoothRiemannianMetric I M) (x : M)
    (A B : Tensor02At (I := I) x) : Real :=
  Tensor0SBundle.inner0S (I := I) (M := M) g x 2 A B


def normSq02
    (g : SmoothRiemannianMetric I M) (x : M)
    (A : Tensor02At (I := I) x) : Real :=
  inner02 (I := I) g x A A

@[simp] theorem normSq02_eq_inner02
    (g : SmoothRiemannianMetric I M) (x : M)
    (A : Tensor02At (I := I) x) :
    normSq02 (I := I) g x A = inner02 (I := I) g x A A := by
  rfl

private theorem norm02_event
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2)
    (x₀ : M) :
    (fun y : M => normSq02 (I := I) g y (A y)) =ᶠ[nhds x₀]
      fun y : M =>
        ∑ i : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
          ∑ j : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
            ∑ k : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
              ∑ l : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
                DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_component
                    (I := I) g x₀ i k (extChartAt I x₀ y) *
                  DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_component
                    (I := I) g x₀ j l (extChartAt I x₀ y) *
                    A y
                      (fun q : Fin 2 =>
                        DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x₀
                          (if q = 0 then i else j) y) *
                      A y
                        (fun q : Fin 2 =>
                          DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x₀
                            (if q = 0 then k else l) y) := by
  classical
  filter_upwards
    [(DifferentialGeometry.Tensor.Coordinates.coordinateFrameSet_open (I := I) x₀).mem_nhds
      (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_mem (I := I) x₀)] with y hy
  let basis := DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_basis (I := I) x₀ hy
  let gInv :
      DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E →
        DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E → Real :=
    fun i j =>
      DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_component
        (I := I) g x₀ i j (extChartAt I x₀ y)
  have hnorm :=
    Tensor0SBundle.normSq0S_two_eq_coord (I := I) (M := M) g y
      basis gInv (DifferentialGeometry.Tensor.Coordinates.gInvBasisAt (I := I) g x₀ hy) (A y)
  calc
    normSq02 (I := I) g y (A y) =
        Tensor0SBundle.normSq0S (I := I) g y 2 (A y) := by
          rfl
    _ =
        ∑ i : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
          ∑ j : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
            ∑ k : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
              ∑ l : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
                gInv i k * gInv j l *
                  A y (fun q : Fin 2 => if q = 0 then basis i else basis j) *
                    A y (fun q : Fin 2 => if q = 0 then basis k else basis l) := hnorm
    _ =
        ∑ i : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
          ∑ j : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
            ∑ k : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
              ∑ l : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
                DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_component
                    (I := I) g x₀ i k (extChartAt I x₀ y) *
                  DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_component
                    (I := I) g x₀ j l (extChartAt I x₀ y) *
                    A y
                      (fun q : Fin 2 =>
                        DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x₀
                          (if q = 0 then i else j) y) *
                      A y
                        (fun q : Fin 2 =>
                          DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x₀
                            (if q = 0 then k else l) y) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          refine Finset.sum_congr rfl fun j _ => ?_
          refine Finset.sum_congr rfl fun k _ => ?_
          refine Finset.sum_congr rfl fun l _ => ?_
          congr 3
          · funext q
            fin_cases q <;>
              simp [basis, DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_basis_apply]
          · funext q
            fin_cases q <;>
              simp [basis, DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_basis_apply]


theorem norm02_smooth
    [CompleteSpace E]
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2) :
    ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
      (fun y : M => normSq02 (I := I) g y (A y)) := by
  classical
  intro x₀
  have hRhs :
      ContMDiffAt I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
        (fun y : M =>
          ∑ i : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
            ∑ j : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
              ∑ k : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
                ∑ l : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E,
                  DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_component
                      (I := I) g x₀ i k (extChartAt I x₀ y) *
                    DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_component
                      (I := I) g x₀ j l (extChartAt I x₀ y) *
                      A y
                        (fun q : Fin 2 =>
                          DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x₀
                            (if q = 0 then i else j) y) *
                        A y
                          (fun q : Fin 2 =>
                            DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt (I := I) x₀
                              (if q = 0 then k else l) y))
        x₀ := by
    refine ContMDiffAt.sum fun i _ => ContMDiffAt.sum fun j _ => ?_
    refine ContMDiffAt.sum fun k _ => ContMDiffAt.sum fun l _ => ?_
    haveI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
      change IsManifold I ∞ M
      infer_instance
    exact
      (((DifferentialGeometry.Tensor.Coordinates.gInvComp_contMDiffAt (I := I) g x₀ i k).mul
        (DifferentialGeometry.Tensor.Coordinates.gInvComp_contMDiffAt (I := I) g x₀ j l)).mul
        (DifferentialGeometry.Tensor.Coordinates.tensor0S_eval_coordinateFrame_contMDiffAt
          (𝕜 := Real) (I := I) (M := M) A x₀
          (fun q : Fin 2 => if q = 0 then i else j))).mul
        (DifferentialGeometry.Tensor.Coordinates.tensor0S_eval_coordinateFrame_contMDiffAt
          (𝕜 := Real) (I := I) (M := M) A x₀
          (fun q : Fin 2 => if q = 0 then k else l))
  exact hRhs.congr_of_eventuallyEq (norm02_event (I := I) g A x₀)


def tensorNormSq02
    (G : RealizedMetricFamily (I := I) (M := M) Time)
    (A : Tensor02Field (I := I) (M := M) Time) :
    Time -> M -> Real :=
  fun t x => normSq02 (I := I) (G.metric t) x (A t x)


def tensor02Comp
    {Idx : Type*}
    (A : Tensor02Field (I := I) (M := M) Time)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Time) (x : M) (i j : Idx) : Real :=
  A t x (fun a => if a = 0 then frame i x else frame j x)




theorem inner02_eq_coord_direct
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : Tensor0SBundle.MetricInverseInBasis_gen (I := I) (M := M) g x basis gInv)
    (A B : Tensor02At (I := I) x) :
    inner02 (I := I) g x A B =
      ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        gInv i k * gInv j l *
          A (vec2 (basis i) (basis j)) *
            B (vec2 (basis k) (basis l)) := by
  simpa [inner02, vec2] using
    Tensor0SBundle.inner0S_two_eq_coord_direct (I := I) (M := M) g x
      basis gInv hinv A B



omit [FiniteDimensional ℝ E] in
theorem metricInverseInBasis_of_frame
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {u : Set M}
    (G : RealizedMetricFamily (I := I) (M := M) Time)
    (gInv : Time -> InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E ∞ frame u)
    (hinv : InverseMetricComponentsInFrameTime (I := I) G gInv frame)
    (t : Time) {x : M} (hx : x ∈ u) :
    Tensor0SBundle.MetricInverseInBasis_gen (I := I) (M := M) (G.metric t) x
      (hframe.toBasisAt hx) (fun i j : Idx => gInv t x i j) := by
  intro i j
  constructor
  · simpa [IsLocalFrameOn.toBasisAt_coe] using (hinv t x i j).1
  · simpa [IsLocalFrameOn.toBasisAt_coe] using (hinv t x i j).2



theorem inner02_eq_coord
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {u : Set M}
    (G : RealizedMetricFamily (I := I) (M := M) Time)
    (A B : Tensor02Field (I := I) (M := M) Time)
    (gInv : Time -> InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E ∞ frame u)
    (hinv : InverseMetricComponentsInFrameTime (I := I) G gInv frame)
    (t : Time) {x : M} (hx : x ∈ u) :
    inner02 (I := I) (G.metric t) x (A t x) (B t x) =
      ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        gInv t x i k * gInv t x j l *
          tensor02Comp (I := I) A frame t x i j *
            tensor02Comp (I := I) B frame t x k l := by
  have hinvAt :
      Tensor0SBundle.MetricInverseInBasis_gen (I := I) (M := M) (G.metric t) x
        (hframe.toBasisAt hx) (fun i j : Idx => gInv t x i j) :=
    metricInverseInBasis_of_frame (I := I) G gInv frame hframe hinv t hx
  simpa [tensor02Comp, vec2, IsLocalFrameOn.toBasisAt_coe] using
    inner02_eq_coord_direct (I := I) (G.metric t) x
      (hframe.toBasisAt hx) (fun i j : Idx => gInv t x i j) hinvAt
      (A t x) (B t x)


theorem normSq02_eq_coord
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {u : Set M}
    (G : RealizedMetricFamily (I := I) (M := M) Time)
    (A : Tensor02Field (I := I) (M := M) Time)
    (gInv : Time -> InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E ∞ frame u)
    (hinv : InverseMetricComponentsInFrameTime (I := I) G gInv frame)
    (t : Time) {x : M} (hx : x ∈ u) :
    tensorNormSq02 (I := I) G A t x =
      ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        gInv t x i k * gInv t x j l *
          tensor02Comp (I := I) A frame t x i j *
            tensor02Comp (I := I) A frame t x k l := by
  have hinvAt :
      Tensor0SBundle.MetricInverseInBasis_gen (I := I) (M := M) (G.metric t) x
        (hframe.toBasisAt hx) (fun i j : Idx => gInv t x i j) :=
    metricInverseInBasis_of_frame (I := I) G gInv frame hframe hinv t hx
  simpa [tensorNormSq02, normSq02, inner02, tensor02Comp,
    IsLocalFrameOn.toBasisAt_coe] using
    Tensor0SBundle.normSq0S_two_eq_coord (I := I) (M := M) (G.metric t) x
      (hframe.toBasisAt hx) (fun i j : Idx => gInv t x i j) hinvAt
      (A t x)

end TensorInner



section GeneralTensorNorm

variable {Comp Dir : Type*} [Fintype Comp] [Fintype Dir]










def tensorNormSqInFrame
    (weight component : Time -> M -> Comp -> Real) :
    Time -> M -> Real :=
  fun t x => ∑ I : Comp, weight t x I * component t x I * component t x I

omit [TopologicalSpace M] in
@[simp] theorem tensorNormSqInFrame_apply
    (weight component : Time -> M -> Comp -> Real)
    (t : Time) (x : M) :
    tensorNormSqInFrame (M := M) weight component t x =
      ∑ I : Comp, weight t x I * component t x I * component t x I := by
  rfl


def roughLapTensorInnerInFrame
    (weight roughLap component : Time -> M -> Comp -> Real) :
    Time -> M -> Real :=
  fun t x => ∑ I : Comp, weight t x I * roughLap t x I * component t x I

omit [TopologicalSpace M] in
@[simp] theorem roughLapTensorInnerInFrame_apply
    (weight roughLap component : Time -> M -> Comp -> Real)
    (t : Time) (x : M) :
    roughLapTensorInnerInFrame (M := M) weight roughLap component t x =
      ∑ I : Comp, weight t x I * roughLap t x I * component t x I := by
  rfl





def nablaTensorNormSqInFrame
    (weight : Time -> M -> Comp -> Real)
    (nablaComponent : Time -> M -> Dir -> Comp -> Real) :
    Time -> M -> Real :=
  fun t x =>
    ∑ a : Dir, ∑ I : Comp,
      weight t x I * nablaComponent t x a I * nablaComponent t x a I

omit [TopologicalSpace M] in
@[simp] theorem nablaTensorNormSqInFrame_apply
    (weight : Time -> M -> Comp -> Real)
    (nablaComponent : Time -> M -> Dir -> Comp -> Real)
    (t : Time) (x : M) :
    nablaTensorNormSqInFrame (M := M) weight nablaComponent t x =
      ∑ a : Dir, ∑ I : Comp,
        weight t x I * nablaComponent t x a I * nablaComponent t x a I := by
  rfl



def ScalarLaplacianRealizesTensorNormBochnerInFrame
    (lapNormSq : Time -> M -> Real)
    (weight roughLap component : Time -> M -> Comp -> Real)
    (nablaComponent : Time -> M -> Dir -> Comp -> Real) : Prop :=
  forall (t : Time) (x : M),
    lapNormSq t x =
      (∑ I : Comp, 2 * (weight t x I * roughLap t x I * component t x I)) +
        (∑ a : Dir, ∑ I : Comp,
          2 * (weight t x I * nablaComponent t x a I * nablaComponent t x a I))


def TensorNormBochnerComponentsInFrame
    (lapNormSq roughLapInner nablaNormSq : Time -> M -> Real) : Prop :=
  forall (t : Time) (x : M),
    lapNormSq t x = 2 * roughLapInner t x + 2 * nablaNormSq t x


omit [TopologicalSpace M] in
theorem tensorNormBochnerComponentsInFrame_of_coordinate_expansion
    (lapNormSq : Time -> M -> Real)
    (weight roughLap component : Time -> M -> Comp -> Real)
    (nablaComponent : Time -> M -> Dir -> Comp -> Real)
    (h_lap : ScalarLaplacianRealizesTensorNormBochnerInFrame
      (M := M) lapNormSq weight roughLap component nablaComponent) :
    TensorNormBochnerComponentsInFrame
      lapNormSq
      (roughLapTensorInnerInFrame (M := M) weight roughLap component)
      (nablaTensorNormSqInFrame (M := M) weight nablaComponent) := by
  intro t x
  rw [h_lap t x]
  unfold roughLapTensorInnerInFrame nablaTensorNormSqInFrame
  let roughTerm : Comp -> Real :=
    fun I => weight t x I * roughLap t x I * component t x I
  let nablaTerm : Dir -> Comp -> Real :=
    fun a I => weight t x I * nablaComponent t x a I * nablaComponent t x a I
  change
      (∑ I : Comp, 2 * roughTerm I) +
          (∑ a : Dir, ∑ I : Comp, 2 * nablaTerm a I) =
        2 * (∑ I : Comp, roughTerm I) +
          2 * (∑ a : Dir, ∑ I : Comp, nablaTerm a I)
  have hrough :
      (∑ I : Comp, 2 * roughTerm I) = 2 * (∑ I : Comp, roughTerm I) := by
    rw [Finset.mul_sum]
  have hnabla :
      (∑ a : Dir, ∑ I : Comp, 2 * nablaTerm a I) =
        2 * (∑ a : Dir, ∑ I : Comp, nablaTerm a I) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum]
  rw [hrough, hnabla]


omit [TopologicalSpace M] in
theorem tensor_norm_laplacian_eq_of_bochner_components
    (lapNormSq roughLapInner nablaNormSq : Time -> M -> Real)
    (h : TensorNormBochnerComponentsInFrame lapNormSq roughLapInner nablaNormSq)
    (t : Time) (x : M) :
    lapNormSq t x = 2 * roughLapInner t x + 2 * nablaNormSq t x :=
  h t x

end GeneralTensorNorm



section RicciNorm

variable {Idx : Type*} [Fintype Idx]



def raisedRicciComponentsInFrame
    (Ric : Time -> RawTwoTensorField (I := I) (M := M))
    (gInv : Time -> InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) :
    Time -> M -> Idx -> Idx -> Real :=
  fun t x i j =>
    ∑ a : Idx, ∑ b : Idx,
      gInv t x i a * gInv t x j b * Ric t x (frame a x) (frame b x)

omit [IsManifold I ∞ M] in
@[simp] theorem raisedRicciComponentsInFrame_apply
    (Ric : Time -> RawTwoTensorField (I := I) (M := M))
    (gInv : Time -> InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Time) (x : M) (i j : Idx) :
    raisedRicciComponentsInFrame (I := I) Ric gInv frame t x i j =
      ∑ a : Idx, ∑ b : Idx,
        gInv t x i a * gInv t x j b * Ric t x (frame a x) (frame b x) := by
  rfl



def ricciNormSqInFrame
    (Ric : Time -> RawTwoTensorField (I := I) (M := M))
    (gInv : Time -> InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) :
    Time -> M -> Real :=
  fun t x =>
    ∑ i : Idx, ∑ j : Idx,
      Ric t x (frame i x) (frame j x) *
        raisedRicciComponentsInFrame (I := I) Ric gInv frame t x i j

omit [IsManifold I ∞ M] in
@[simp] theorem ricciNormSqInFrame_apply
    (Ric : Time -> RawTwoTensorField (I := I) (M := M))
    (gInv : Time -> InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Time) (x : M) :
    ricciNormSqInFrame (I := I) Ric gInv frame t x =
      ∑ i : Idx, ∑ j : Idx,
        Ric t x (frame i x) (frame j x) *
          raisedRicciComponentsInFrame (I := I) Ric gInv frame t x i j := by
  rfl


def roughLapRicciInnerInFrame
    (roughLapRic : Time -> M -> Idx -> Idx -> Real)
    (Ric : Time -> RawTwoTensorField (I := I) (M := M))
    (gInv : Time -> InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) :
    Time -> M -> Real :=
  fun t x =>
    ∑ i : Idx, ∑ j : Idx,
      roughLapRic t x i j *
        raisedRicciComponentsInFrame (I := I) Ric gInv frame t x i j

omit [IsManifold I ∞ M] in
@[simp] theorem roughLapRicciInnerInFrame_apply
    (roughLapRic : Time -> M -> Idx -> Idx -> Real)
    (Ric : Time -> RawTwoTensorField (I := I) (M := M))
    (gInv : Time -> InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Time) (x : M) :
    roughLapRicciInnerInFrame (I := I) roughLapRic Ric gInv frame t x =
      ∑ i : Idx, ∑ j : Idx,
        roughLapRic t x i j *
          raisedRicciComponentsInFrame (I := I) Ric gInv frame t x i j := by
  rfl



def nablaRicciNormSqInFrame
    (nablaRic : Time -> M -> Idx -> Idx -> Idx -> Real)
    (gInv : Time -> InverseMetricComponents M Idx) :
    Time -> M -> Real :=
  fun t x =>
    ∑ a : Idx, ∑ b : Idx, ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      gInv t x a b * gInv t x i k * gInv t x j l *
        nablaRic t x a i j * nablaRic t x b k l

omit [TopologicalSpace M] in
@[simp] theorem nablaRicciNormSqInFrame_apply
    (nablaRic : Time -> M -> Idx -> Idx -> Idx -> Real)
    (gInv : Time -> InverseMetricComponents M Idx)
    (t : Time) (x : M) :
    nablaRicciNormSqInFrame (M := M) nablaRic gInv t x =
      ∑ a : Idx, ∑ b : Idx, ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        gInv t x a b * gInv t x i k * gInv t x j l *
          nablaRic t x a i j * nablaRic t x b k l := by
  rfl



section Tensor02Product

variable [FiniteDimensional Real E]

omit [FiniteDimensional ℝ E] in
private theorem tensor0S_curry_apply_cons_local
    {x : M} (s : ℕ)
    (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 1) x)
    (X : TangentSpace I x) (tail : Fin s -> TangentSpace I x) :
    (tensor0S_curry (I := I) (𝕜 := Real) (M := M) s x A X) tail =
      A (Fin.cons X tail) := by
  change
    (((continuousMultilinearCurryLeftEquiv Real
        (fun _ : Fin (s + 1) => E) Real)
        ((tensor0SSpace_continuousLinearEquiv (I := I) (M := M) (s + 1) x) A)
        X)
        tail) =
      ((tensor0SSpace_continuousLinearEquiv (I := I) (M := M) (s + 1) x) A)
        (Fin.cons X tail)
  rw [continuousMultilinearCurryLeftEquiv_apply]

omit [IsManifold I ∞ M] [FiniteDimensional ℝ E] in
private theorem fin_cons_vec2_eq_vec3
    {x : M} (X Y Z : TangentSpace I x) :
    Fin.cons X (vec2 (I := I) Y Z) =
      vec3 (I := I) X Y Z := by
  funext a
  fin_cases a <;> rfl

omit [IsManifold I ∞ M] [FiniteDimensional ℝ E] in
private theorem fin_cons_vec3_eq_vec4
    {x : M} (X Y Z W : TangentSpace I x) :
    Fin.cons X (vec3 (I := I) Y Z W) =
      vec4 (I := I) X Y Z W := by
  funext a
  fin_cases a <;> rfl

omit [IsManifold I ∞ M] [FiniteDimensional ℝ E] in
private theorem metricTraceInput_vec2_eq_vec4
    {x : M} (X Y Z W : TangentSpace I x) :
    metricTraceInput (I := I) X Y (vec2 (I := I) Z W) =
      vec4 (I := I) X Y Z W := by
  funext a
  fin_cases a <;> rfl

private theorem sum_six_rotate_two
    {Idx A : Type*} [Fintype Idx] [AddCommMonoid A]
    (F : Idx -> Idx -> Idx -> Idx -> Idx -> Idx -> A) :
    (∑ a : Idx, ∑ b : Idx, ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        F a b i j k l) =
      ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx, ∑ a : Idx, ∑ b : Idx,
        F a b i j k l := by
  calc
    (∑ a : Idx, ∑ b : Idx, ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        F a b i j k l)
        =
      ∑ a : Idx, ∑ i : Idx, ∑ b : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        F a b i j k l := by
          apply Finset.sum_congr rfl
          intro a _
          rw [Finset.sum_comm]
    _ =
      ∑ i : Idx, ∑ a : Idx, ∑ b : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        F a b i j k l := by
          rw [Finset.sum_comm]
    _ =
      ∑ i : Idx, ∑ a : Idx, ∑ j : Idx, ∑ b : Idx, ∑ k : Idx, ∑ l : Idx,
        F a b i j k l := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro a _
          rw [Finset.sum_comm]
    _ =
      ∑ i : Idx, ∑ j : Idx, ∑ a : Idx, ∑ b : Idx, ∑ k : Idx, ∑ l : Idx,
        F a b i j k l := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_comm]
    _ =
      ∑ i : Idx, ∑ j : Idx, ∑ a : Idx, ∑ k : Idx, ∑ b : Idx, ∑ l : Idx,
        F a b i j k l := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          apply Finset.sum_congr rfl
          intro a _
          rw [Finset.sum_comm]
    _ =
      ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ a : Idx, ∑ b : Idx, ∑ l : Idx,
        F a b i j k l := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.sum_comm]
    _ =
      ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ a : Idx, ∑ l : Idx, ∑ b : Idx,
        F a b i j k l := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          apply Finset.sum_congr rfl
          intro k _
          apply Finset.sum_congr rfl
          intro a _
          rw [Finset.sum_comm]
    _ =
      ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx, ∑ a : Idx, ∑ b : Idx,
        F a b i j k l := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          apply Finset.sum_congr rfl
          intro k _
          rw [Finset.sum_comm]

private theorem sum_trace_tensor02_rough
    {Idx : Type*} [Fintype Idx]
    (G A : Idx -> Idx -> Real)
    (B : Idx -> Idx -> Idx -> Idx -> Real) :
    (∑ a : Idx, ∑ b : Idx,
        G a b *
          (∑ i : Idx, ∑ j : Idx,
            B a b i j *
              (∑ k : Idx, ∑ l : Idx, G i k * G j l * A k l))) =
      ∑ i : Idx, ∑ j : Idx,
        (∑ a : Idx, ∑ b : Idx, G a b * B a b i j) *
          (∑ k : Idx, ∑ l : Idx, G i k * G j l * A k l) := by
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [sum_six_rotate_two]
  simp [mul_left_comm, mul_comm]

private theorem sum_trace_tensor02_nabla
    {Idx : Type*} [Fintype Idx]
    (G : Idx -> Idx -> Real)
    (B : Idx -> Idx -> Idx -> Real) :
    (∑ a : Idx, ∑ b : Idx,
        G a b *
          (∑ i : Idx, ∑ j : Idx,
            B a i j *
              (∑ k : Idx, ∑ l : Idx, G i k * G j l * B b k l))) =
      ∑ a : Idx, ∑ b : Idx, ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        G a b * G i k * G j l * B a i j * B b k l := by
  simp_rw [Finset.mul_sum]
  simp [mul_left_comm, mul_comm]


def tensor02RoughInnerCoord
    {Idx : Type*} [Fintype Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (A roughA : Tensor02At (I := I) x) : Real :=
  ∑ i : Idx, ∑ j : Idx,
    roughA (vec2 (I := I) (basis i) (basis j)) *
      (∑ k : Idx, ∑ l : Idx,
        gInv i k * gInv j l *
          A (vec2 (I := I) (basis k) (basis l)))


def tensor02NablaNormCoord
    {Idx : Type*} [Fintype Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (nablaA : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x) :
    Real :=
  ∑ a : Idx, ∑ b : Idx, ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
    gInv a b * gInv i k * gInv j l *
      nablaA (vec3 (I := I) (basis a) (basis i) (basis j)) *
        nablaA (vec3 (I := I) (basis b) (basis k) (basis l))



theorem inner02_rough
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M)
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : Tensor0SBundle.MetricInverseInBasis_gen (I := I) (M := M) g x basis gInv)
    (A B : Tensor02At (I := I) x) :
    inner02 (I := I) g x B A =
      tensor02RoughInnerCoord (I := I) basis gInv A B := by
  classical
  rw [inner02_eq_coord_direct (I := I) g x basis gInv hinv B A]
  unfold tensor02RoughInnerCoord
  simp_rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  refine Finset.sum_congr rfl fun l _ => ?_
  ring


def tensor02FreezeNabla
    {x : M}
    (nablaA : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (X : TangentSpace I x) : Tensor02At (I := I) x :=
  freezeLastTwo0S3 (I := I) nablaA X

omit [FiniteDimensional ℝ E] in
@[simp] theorem tensor02FreezeNabla_apply
    {x : M}
    (nablaA : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (X Y Z : TangentSpace I x) :
    tensor02FreezeNabla (I := I) nablaA X (vec2 (I := I) Y Z) =
      nablaA (vec3 (I := I) X Y Z) := by
  exact freezeLastTwo0S3_apply (I := I) nablaA X Y Z

omit [FiniteDimensional ℝ E] in
theorem tensor02FreezeNabla_eq_curry
    {x : M}
    (nablaA : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (X : TangentSpace I x) :
    tensor02FreezeNabla (I := I) nablaA X =
      tensor0S_curry (I := I) (𝕜 := Real) (M := M) 2 x nablaA X := by
  ext v
  have hv : v = vec2 (I := I) (v 0) (v 1) := by
    funext a
    fin_cases a <;> rfl
  rw [hv, tensor02FreezeNabla_apply, tensor0S_curry_apply_cons_local]
  congr 1
  exact (fin_cons_vec2_eq_vec3 (I := I) X (v 0) (v 1)).symm



noncomputable def freeze02Field
    (nablaA :
      Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) 3)
    (Y : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _)) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2 := by
  letI := tensor0SBundle_topology (𝕜 := Real) (E := E) (H := H)
    (I := I) (M := M) 2
  refine ⟨fun y : M => tensor02FreezeNabla (I := I) (nablaA y) (Y y), ?_⟩
  intro x₀
  have hnabla := nablaA.contMDiff x₀
  have hcurry :=
    TensorMultilinear.contMDiffAt_curriedSection_of_contMDiffAt_section_gen
      (𝕜 := Real) (I := I) (M := M)
      (T := fun y : M => nablaA y) x₀ hnabla
  have hY := Y.contMDiff x₀
  have happ : ContMDiffAt I
      (I.prod 𝓘(Real, Tensor0SModel 2 Real E)) (∞ : WithTop ℕ∞)
      (fun y : M =>
        TotalSpace.mk' (Tensor0SModel 2 Real E)
          (E := fun x : M => Tensor0SSpace 2 I x) y
          ((TensorMultilinear.curriedSection_gen (𝕜 := Real) (I := I) (M := M)
            (fun z : M => nablaA z) y) (Y y))) x₀ :=
    ContMDiffAt.clm_bundle_apply (𝕜 := Real) (n := (∞ : WithTop ℕ∞))
      (F₁ := E) (F₂ := Tensor0SModel 2 Real E)
      (E₁ := fun x : M => TangentSpace I x)
      (E₂ := fun x : M => Tensor0SSpace 2 I x)
      (IM := I) (IB := I)
      (b := id)
      (ϕ := fun y : M =>
        TensorMultilinear.curriedSection_gen (𝕜 := Real) (I := I) (M := M)
          (fun z : M => nablaA z) y)
      (v := fun y : M => Y y) hcurry hY
  refine happ.congr_of_eventuallyEq ?_
  filter_upwards with y
  simpa [TensorMultilinear.curriedSection_gen] using
    tensor02FreezeNabla_eq_curry (I := I) (nablaA y) (Y y)

@[simp] theorem freeze02Field_apply
    (nablaA :
      Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) 3)
    (Y : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (x : M) :
    freeze02Field (I := I) nablaA Y x =
      tensor02FreezeNabla (I := I) (nablaA x) (Y x) := by
  change (fun y : M => tensor02FreezeNabla (I := I) (nablaA y) (Y y)) x =
    tensor02FreezeNabla (I := I) (nablaA x) (Y x)
  rfl







theorem tensor02_inner_extDerivFun_eq_inner_nabla
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    (hmc : DifferentialGeometry.Integral.Connection.IsMetricCompatible_gen (I := I) cov g)
    (A B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2)
    (nablaA nablaB :
      Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) 3)
    (hA : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I)
      (M := M) 2 cov A nablaA)
    (hB : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I)
      (M := M) 2 cov B nablaB)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (x : M) :
    extDerivFun (I := I)
      (fun y : M => inner02 (I := I) g y (A y) (B y)) x (X x) =
      inner02 (I := I) g x
        (tensor02FreezeNabla (I := I) (nablaA x) (X x)) (B x) +
        inner02 (I := I) g x (A x)
          (tensor02FreezeNabla (I := I) (nablaB x) (X x)) := by
  have h :=
    Tensor0SBundle.inner0S_two_metricCompatible_extDerivFun (I := I)
      cov g hmc A B nablaA nablaB hA hB X x
  have hfreezeA :
      tensor02FreezeNabla (I := I) (nablaA x) (X x) =
        tensor0S_curry (I := I) (𝕜 := Real) (M := M) 2 x
          (nablaA x) (X x) :=
    tensor02FreezeNabla_eq_curry (I := I) (nablaA x) (X x)
  have hfreezeB :
      tensor02FreezeNabla (I := I) (nablaB x) (X x) =
        tensor0S_curry (I := I) (𝕜 := Real) (M := M) 2 x
          (nablaB x) (X x) :=
    tensor02FreezeNabla_eq_curry (I := I) (nablaB x) (X x)
  simpa [inner02, hfreezeA, hfreezeB] using h


theorem inner02_symm
    (g : SmoothRiemannianMetric I M) (x : M)
    (A B : Tensor02At (I := I) x) :
    inner02 (I := I) g x A B = inner02 (I := I) g x B A := by
  simpa [inner02, Tensor0SBundle.inner0S] using
    (Tensor0SBundle.MetricFiberData.inner_comm
      (Tensor0SBundle.tensor0SMetricData (I := I) g x 2) A B)

private theorem inner02_mdiff
    (g : SmoothRiemannianMetric I M)
    (A B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2)
    (x : M) :
    MDifferentiableAt I 𝓘(Real, Real)
      (fun y : M => inner02 (I := I) g y (A y) (B y)) x := by
  simpa [inner02] using
    Tensor0SBundle.inner0S_two_mdiff (I := I) g A B x

private theorem inner02_nablaFun
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    (hmc : DifferentialGeometry.Integral.Connection.IsMetricCompatible_gen (I := I) cov g)
    (A B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (x : M) :
    extDerivFun (I := I)
        (fun y : M => inner02 (I := I) g y (A y) (B y)) x (X x) =
      inner02 (I := I) g x
        (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          2 cov X A x) (B x) +
        inner02 (I := I) g x (A x)
          (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            2 cov X B x) := by
  simpa [inner02] using
    Tensor0SBundle.inner0S_two_nabla (I := I) cov g hmc A B X x

private theorem eval_pt0S
    [T2Space M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    {s : Nat} {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s}
    {nablaA : Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (s + 1)}
    (hA : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) s cov A nablaA)
    {x : M} (W : TangentSpace I x)
    (V : Fin s -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _)) :
    nablaA x (Fin.cons W (fun q : Fin s => V q x)) =
      extDerivFun (I := I)
        (fun y : M => A y (fun q : Fin s => V q y)) x W -
      ∑ q : Fin s,
        A x
          (Function.update (fun r : Fin s => V r x) q
            ((cov (fun y : M => V q y) x) W)) := by
  obtain ⟨Wsec, hWsec⟩ :=
    ContMDiffSection.exists_eq_at_gen
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x W
  have h0 := TotalNabla0SRealizes.eval_smooth_slots
    (I := I) hA Wsec V x
  simpa [hWsec] using h0



theorem du_norm02
    [T2Space M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    (hmc : DifferentialGeometry.Integral.Connection.IsMetricCompatible_gen (I := I) cov g)
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2)
    (nablaA :
      Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) 3)
    (hA : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 2 cov A nablaA)
    (du : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1)
    (hdu : DuFieldRealizes (I := I)
      (fun y : M => normSq02 (I := I) g y (A y)) du)
    {x : M} (W : TangentSpace I x) :
    du x (fun _ : Fin 1 => W) =
      2 * inner02 (I := I) g x
        (tensor02FreezeNabla (I := I) (nablaA x) W) (A x) := by
  obtain ⟨Wsec, hWsec⟩ :=
    ContMDiffSection.exists_eq_at_gen
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x W
  have hinner :=
    tensor02_inner_extDerivFun_eq_inner_nabla
      (I := I) cov g hmc A A nablaA nablaA hA hA Wsec x
  calc
    du x (fun _ : Fin 1 => W)
        = differential1FormFun (I := I)
            (fun y : M => normSq02 (I := I) g y (A y)) x
            (fun _ : Fin 1 => W) := by
              rw [hdu x]
              rfl
    _ = extDerivFun (I := I)
          (fun y : M => normSq02 (I := I) g y (A y)) x W := by
          exact differential1FormFun_apply_eq_extDerivFun
            (I := I) (fun y : M => normSq02 (I := I) g y (A y)) x W
    _ = extDerivFun (I := I)
          (fun y : M => inner02 (I := I) g y (A y) (A y)) x (Wsec x) := by
          simp [normSq02, hWsec]
    _ =
      inner02 (I := I) g x
        (tensor02FreezeNabla (I := I) (nablaA x) (Wsec x)) (A x) +
      inner02 (I := I) g x (A x)
        (tensor02FreezeNabla (I := I) (nablaA x) (Wsec x)) := hinner
    _ = 2 * inner02 (I := I) g x
        (tensor02FreezeNabla (I := I) (nablaA x) W) (A x) := by
          rw [hWsec]
          rw [inner02_symm (I := I) g x (A x)
            (tensor02FreezeNabla (I := I) (nablaA x) W)]
          ring


def tensor02FreezeNabla2
    {x : M}
    (nabla2A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 x)
    (X Y : TangentSpace I x) : Tensor02At (I := I) x :=
  freezeLastTwo0S3 (I := I)
    (tensor0S_curry (I := I) (𝕜 := Real) (M := M) 3 x nabla2A X) Y

omit [FiniteDimensional ℝ E] in
@[simp] theorem tensor02FreezeNabla2_apply
    {x : M}
    (nabla2A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 x)
    (X Y Z W : TangentSpace I x) :
    tensor02FreezeNabla2 (I := I) nabla2A X Y (vec2 (I := I) Z W) =
      nabla2A (vec4 (I := I) X Y Z W) := by
  unfold tensor02FreezeNabla2
  rw [freezeLastTwo0S3_apply]
  change Tensor0SSpace.toModel
      (tensor0S_curry (I := I) (𝕜 := Real) (M := M) 3 x nabla2A X)
      (vec3 (I := I) Y Z W) =
    Tensor0SSpace.toModel nabla2A (vec4 (I := I) X Y Z W)
  rw [TensorMultilinear.tensor0S_curry_apply_eval_gen]
  congr 1
  exact fin_cons_vec3_eq_vec4 (I := I) X Y Z W

set_option linter.flexible false in





theorem freeze02_deriv
    [T2Space M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    (hmc : DifferentialGeometry.Integral.Connection.IsMetricCompatible_gen (I := I) cov g)
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2)
    (nablaA :
      Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) 3)
    (nabla2A :
      Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) 4)
    (hA : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 2 cov A nablaA)
    (h2 : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 3 cov nablaA nabla2A)
    (X Y : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (x : M) :
    extDerivFun (I := I)
        (fun y : M =>
          2 * inner02 (I := I) g y
            (tensor02FreezeNabla (I := I) (nablaA y) (Y y)) (A y))
        x (X x) =
      2 *
        (inner02 (I := I) g x
            (tensor02FreezeNabla2 (I := I) (nabla2A x) (X x) (Y x))
            (A x) +
          inner02 (I := I) g x
            (tensor02FreezeNabla (I := I) (nablaA x)
              ((cov (fun y : M => Y y) x) (X x))) (A x) +
          inner02 (I := I) g x
            (tensor02FreezeNabla (I := I) (nablaA x) (Y x))
            (tensor02FreezeNabla (I := I) (nablaA x) (X x))) := by
  let B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2 :=
    freeze02Field (I := I) nablaA Y
  have hf :
      MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => inner02 (I := I) g y (B y) (A y)) x :=
    inner02_mdiff (I := I) g B A x
  have hscale := congrArg (fun L => L (X x))
    (extDerivFun_const_mul I (2 : Real) hf)
  have hinner := inner02_nablaFun (I := I) cov g hmc B A X x
  have hAderiv :
      nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          2 cov X A x =
        tensor02FreezeNabla (I := I) (nablaA x) (X x) := by
    ext v
    calc
      (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          2 cov X A x) v =
          nablaA x (Fin.cons (X x) v) := by
            exact (TotalNabla0SRealizes.apply (I := I) hA X x v).symm
      _ = tensor02FreezeNabla (I := I) (nablaA x) (X x) v := by
            rw [tensor02FreezeNabla_eq_curry]
            simp [tensor0S_curry_apply_cons_local]
  have hBderiv :
      nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          2 cov X B x =
        tensor02FreezeNabla2 (I := I) (nabla2A x) (X x) (Y x) +
          tensor02FreezeNabla (I := I) (nablaA x)
            ((cov (fun y : M => Y y) x) (X x)) := by
    ext v
    have hv : v = vec2 (I := I) (v 0) (v 1) := by
      funext a
      fin_cases a <;> rfl
    obtain ⟨Z, hZ⟩ :=
      ContMDiffSection.exists_eq_at_gen
        (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x (v 0)
    obtain ⟨W, hW⟩ :=
      ContMDiffSection.exists_eq_at_gen
        (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x (v 1)
    let V2 : Fin 2 -> ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M -> Type _) :=
      fun a => if a = 0 then Z else W
    let V3 : Fin 3 -> ContMDiffSection I E (∞ : WithTop ℕ∞)
        (TangentSpace I : M -> Type _) :=
      Fin.cons Y V2
    have hV2x : (fun a : Fin 2 => V2 a x) = v := by
      funext a
      fin_cases a <;> simp [V2, hZ, hW]
    have hfree_raw :=
      Tensor0SBundle.nabla0SFun_eval_smooth_slots
        (I := I) cov X V2 B x
    have htot_raw :=
      TotalNabla0SRealizes.eval_smooth_slots
        (I := I) h2 X V3 x
    let D : Real :=
      extDerivFun (I := I)
        (fun p : M => nablaA p (fun a : Fin 3 => V3 a p)) x (X x)
    let CY : Real :=
      nablaA x
        (vec3 (I := I) ((cov (fun y : M => Y y) x) (X x)) (v 0) (v 1))
    let CZ : Real :=
      nablaA x
        (vec3 (I := I) (Y x) ((cov (fun y : M => Z y) x) (X x)) (v 1))
    let CW : Real :=
      nablaA x
        (vec3 (I := I) (Y x) (v 0) ((cov (fun y : M => W y) x) (X x)))
    have hDfree :
        extDerivFun (I := I)
            (fun p : M => B p (fun a : Fin 2 => V2 a p)) x (X x) = D := by
      exact DifferentialGeometry.Tensor.Coordinates.deriv_congr_nhds
        (I := I) (X x)
        (by
          filter_upwards with p
          dsimp [B, D, V3, freeze02Field_apply]
          rw [freeze02Field_apply]
          rw [tensor02FreezeNabla_eq_curry, tensor0S_curry_apply_cons_local]
          congr 1
          funext a
          cases a using Fin.cases <;> simp [Fin.cons_zero, Fin.cons_succ])
    have hV3x :
        (fun a : Fin 3 => V3 a x) = vec3 (I := I) (Y x) (v 0) (v 1) := by
      have hcons :
          (fun a : Fin 3 => V3 a x) =
            Fin.cons (Y x) (fun a : Fin 2 => V2 a x) := by
        funext a
        fin_cases a <;> rfl
      calc
        (fun a : Fin 3 => V3 a x) =
            Fin.cons (Y x) (fun a : Fin 2 => V2 a x) := hcons
        _ = Fin.cons (Y x) v := by rw [hV2x]
        _ = Fin.cons (Y x) (vec2 (I := I) (v 0) (v 1)) := by
              funext a
              fin_cases a <;> rfl
        _ = vec3 (I := I) (Y x) (v 0) (v 1) :=
              fin_cons_vec2_eq_vec3 (I := I) (Y x) (v 0) (v 1)
    have h4 :
        Fin.cons (X x) (fun a : Fin 3 => V3 a x) =
          vec4 (I := I) (X x) (Y x) (v 0) (v 1) := by
      rw [hV3x]
      exact fin_cons_vec3_eq_vec4 (I := I) (X x) (Y x) (v 0) (v 1)
    have hfree :
        (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            2 cov X B x) v = D - (CZ + CW) := by
      rw [← hV2x]
      have h := hfree_raw
      rw [hDfree] at h
      simp [B, freeze02Field_apply,
        tensor02FreezeNabla_eq_curry, tensor0S_curry_apply_cons_local,
        Fin.sum_univ_two, V2] at h
      have hZupd :
          Function.update
              (Fin.cons (Y x) (fun a : Fin 2 => (if a = 0 then Z else W) x)) 1
              ((cov (fun p : M => Z p) x) (X x)) =
            vec3 (I := I) (Y x) ((cov (fun y : M => Z y) x) (X x)) (v 1) := by
        funext a
        fin_cases a
        · simp [Function.update, DifferentialGeometry.Integral.Connection.vec3]
        · simp [Function.update, DifferentialGeometry.Integral.Connection.vec3]
        · simpa [Function.update, DifferentialGeometry.Integral.Connection.vec3] using hW
      have hWupd :
          Function.update
              (Fin.cons (Y x) (fun a : Fin 2 => (if a = 0 then Z else W) x)) 2
              ((cov (fun p : M => W p) x) (X x)) =
            vec3 (I := I) (Y x) (v 0) ((cov (fun y : M => W y) x) (X x)) := by
        funext a
        fin_cases a
        · simp [Function.update, DifferentialGeometry.Integral.Connection.vec3]
        · simpa [Function.update, DifferentialGeometry.Integral.Connection.vec3] using hZ
        · simp [Function.update, DifferentialGeometry.Integral.Connection.vec3]
      rw [hZupd, hWupd] at h
      simpa [CZ, CW] using h
    have htot :
        tensor02FreezeNabla2 (I := I) (nabla2A x) (X x) (Y x) v =
          D - (CY + CZ + CW) := by
      rw [hv]
      have h := htot_raw
      rw [h4] at h
      rw [hV3x] at h
      have hYupd :
          Function.update (vec3 (I := I) (Y x) (v 0) (v 1)) 0
              ((cov (fun p : M => Y p) x) (X x)) =
            vec3 (I := I) ((cov (fun y : M => Y y) x) (X x)) (v 0) (v 1) := by
        funext a
        fin_cases a <;> simp [Function.update, DifferentialGeometry.Integral.Connection.vec3]
      have hZupd3 :
          Function.update (vec3 (I := I) (Y x) (v 0) (v 1)) 1
              ((cov (fun p : M => Z p) x) (X x)) =
            vec3 (I := I) (Y x) ((cov (fun y : M => Z y) x) (X x)) (v 1) := by
        funext a
        fin_cases a <;> simp [Function.update, DifferentialGeometry.Integral.Connection.vec3]
      have hWupd3 :
          Function.update (vec3 (I := I) (Y x) (v 0) (v 1)) 2
              ((cov (fun p : M => W p) x) (X x)) =
            vec3 (I := I) (Y x) (v 0) ((cov (fun y : M => W y) x) (X x)) := by
        funext a
        fin_cases a <;> simp [Function.update, DifferentialGeometry.Integral.Connection.vec3]
      simp [Fin.sum_univ_succ, V3, V2] at h
      rw [hYupd, hZupd3, hWupd3] at h
      have h' :
          (nabla2A x) (vec4 (I := I) (X x) (Y x) (v 0) (v 1)) =
            D - (CY + (CZ + CW)) := by
        simpa [D, CY, CZ, CW, V2, V3, hZ, hW,
          DifferentialGeometry.Integral.Connection.vec2, DifferentialGeometry.Integral.Connection.vec3,
          DifferentialGeometry.Integral.Connection.vec4, Fin.sum_univ_succ, Fin.sum_univ_two,
          Function.update, Fin.cons_zero, Fin.cons_succ]
          using h
      calc
        tensor02FreezeNabla2 (I := I) (nabla2A x) (X x) (Y x)
            (vec2 (I := I) (v 0) (v 1)) =
          (nabla2A x) (vec4 (I := I) (X x) (Y x) (v 0) (v 1)) := by
            rw [tensor02FreezeNabla2_apply]
        _ = D - (CY + (CZ + CW)) := h'
        _ = D - (CY + CZ + CW) := by ring
    have hCY :
        tensor02FreezeNabla (I := I) (nablaA x)
            ((cov (fun y : M => Y y) x) (X x)) v = CY := by
      rw [hv]
      rw [tensor02FreezeNabla_eq_curry, tensor0S_curry_apply_cons_local]
      change
        nablaA x
            (Fin.cons ((cov (fun y : M => Y y) x) (X x))
              (vec2 (I := I) (v 0) (v 1))) = CY
      rw [fin_cons_vec2_eq_vec3]
    calc
      (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          2 cov X B x) v = D - (CZ + CW) := hfree
      _ =
          tensor02FreezeNabla2 (I := I) (nabla2A x) (X x) (Y x) v +
          tensor02FreezeNabla (I := I) (nablaA x)
              ((cov (fun y : M => Y y) x) (X x)) v := by
          rw [htot, hCY]
          ring
  calc
    extDerivFun (I := I)
        (fun y : M =>
          2 * inner02 (I := I) g y
            (tensor02FreezeNabla (I := I) (nablaA y) (Y y)) (A y))
        x (X x)
        =
      2 * extDerivFun (I := I)
        (fun y : M => inner02 (I := I) g y (B y) (A y)) x (X x) := by
        simpa [B, Pi.smul_apply, smul_eq_mul] using hscale
    _ =
      2 *
        (inner02 (I := I) g x
            (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
              2 cov X B x) (A x) +
          inner02 (I := I) g x (B x)
            (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
              2 cov X A x)) := by
        rw [hinner]
    _ =
      2 *
        (inner02 (I := I) g x
            (tensor02FreezeNabla2 (I := I) (nabla2A x) (X x) (Y x))
            (A x) +
          inner02 (I := I) g x
            (tensor02FreezeNabla (I := I) (nablaA x)
              ((cov (fun y : M => Y y) x) (X x))) (A x) +
          inner02 (I := I) g x
            (tensor02FreezeNabla (I := I) (nablaA x) (Y x))
            (tensor02FreezeNabla (I := I) (nablaA x) (X x))) := by
        rw [hAderiv, hBderiv]
        simp [B, inner02, Tensor0SBundle.inner0S, map_add]



def Tensor02NormHessianProductInBasis
    {Idx : Type*} [Fintype Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (A : Tensor02At (I := I) x)
    (nablaA : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (nabla2A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 x)
    (normSecond : Tensor02At (I := I) x) : Prop :=
  ∀ i j : Idx,
    normSecond (vec2 (I := I) (basis i) (basis j)) =
      (2 : Real) *
        (tensor02RoughInnerCoord (I := I) basis gInv A
            (tensor02FreezeNabla2 (I := I) nabla2A (basis i) (basis j)) +
          tensor02RoughInnerCoord (I := I) basis gInv
            (tensor02FreezeNabla (I := I) nablaA (basis j))
            (tensor02FreezeNabla (I := I) nablaA (basis i)))



theorem hess_norm02
    [T2Space M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    (hmc : DifferentialGeometry.Integral.Connection.IsMetricCompatible_gen (I := I) cov g)
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : Tensor0SBundle.MetricInverseInBasis_gen (I := I) (M := M) g x basis gInv)
    (X : Idx -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (hfields : SmoothBasisFieldsAt (I := I) basis X)
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2)
    (nablaA :
      Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) 3)
    (nabla2A :
      Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) 4)
    (hA : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 2 cov A nablaA)
    (h2 : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 3 cov nablaA nabla2A)
    (du : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1)
    (normSecond : (y : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 y)
    (hdu : DuFieldRealizes (I := I)
      (fun y : M => normSq02 (I := I) g y (A y)) du)
    (hHess : HessianRealizesNablaDuAt (I := I) cov du normSecond x) :
    Tensor02NormHessianProductInBasis (I := I) basis gInv (A x) (nablaA x)
      (nabla2A x) (normSecond x) := by
  classical
  intro i j
  have hfun :
      (fun y : M => du y (fun _ : Fin 1 => X j y)) =
        fun y : M =>
          2 * inner02 (I := I) g y
            (tensor02FreezeNabla (I := I) (nablaA y) (X j y)) (A y) := by
    funext y
    exact du_norm02 (I := I) cov g hmc A nablaA hA du hdu (X j y)
  have hnablaDu :
      nablaDuAt (I := I) cov (X i) du x (fun _ : Fin 1 => basis j) =
        extDerivFun (I := I) (fun y : M => du y (fun _ : Fin 1 => X j y))
          x (X i x) -
        du x (fun _ : Fin 1 => (cov (fun y : M => X j y) x) (X i x)) := by
    have h := DifferentialGeometry.Tensor.Coordinates.nabla0SFun_one_eval_smooth_slots
      (I := I) cov (X i) (X j) du x
    simpa [nablaDuAt, hfields j] using h
  have hder := freeze02_deriv (I := I) cov g hmc A nablaA nabla2A hA h2
    (X i) (X j) x
  have hcorr := du_norm02 (I := I) cov g hmc A nablaA hA du hdu
    ((cov (fun y : M => X j y) x) (X i x))
  have hraw :
      normSecond x (vec2 (I := I) (basis i) (basis j)) =
        2 *
          (inner02 (I := I) g x
              (tensor02FreezeNabla2 (I := I) (nabla2A x) (basis i) (basis j))
              (A x) +
            inner02 (I := I) g x
              (tensor02FreezeNabla (I := I) (nablaA x) (basis j))
              (tensor02FreezeNabla (I := I) (nablaA x) (basis i))) := by
    calc
      normSecond x (vec2 (I := I) (basis i) (basis j))
          = normSecond x (vec2 (I := I) (X i x) (basis j)) := by
              rw [hfields i]
      _ = nablaDuAt (I := I) cov (X i) du x (fun _ : Fin 1 => basis j) := by
              exact hHess (X i) (basis j)
      _ =
          extDerivFun (I := I) (fun y : M => du y (fun _ : Fin 1 => X j y))
            x (X i x) -
          du x (fun _ : Fin 1 => (cov (fun y : M => X j y) x) (X i x)) := hnablaDu
      _ =
          extDerivFun (I := I)
            (fun y : M =>
              2 * inner02 (I := I) g y
                (tensor02FreezeNabla (I := I) (nablaA y) (X j y)) (A y))
            x (X i x) -
          du x (fun _ : Fin 1 => (cov (fun y : M => X j y) x) (X i x)) := by
            rw [hfun]
      _ =
          2 *
            (inner02 (I := I) g x
                (tensor02FreezeNabla2 (I := I) (nabla2A x) (basis i) (basis j))
                (A x) +
              inner02 (I := I) g x
                (tensor02FreezeNabla (I := I) (nablaA x) (basis j))
                (tensor02FreezeNabla (I := I) (nablaA x) (basis i))) := by
            rw [hder, hcorr, hfields i, hfields j]
            ring
  calc
    normSecond x (vec2 (I := I) (basis i) (basis j))
        =
      2 *
        (inner02 (I := I) g x
            (tensor02FreezeNabla2 (I := I) (nabla2A x) (basis i) (basis j))
            (A x) +
          inner02 (I := I) g x
            (tensor02FreezeNabla (I := I) (nablaA x) (basis j))
            (tensor02FreezeNabla (I := I) (nablaA x) (basis i))) := hraw
    _ =
      (2 : Real) *
        (tensor02RoughInnerCoord (I := I) basis gInv (A x)
            (tensor02FreezeNabla2 (I := I) (nabla2A x) (basis i) (basis j)) +
          tensor02RoughInnerCoord (I := I) basis gInv
            (tensor02FreezeNabla (I := I) (nablaA x) (basis j))
            (tensor02FreezeNabla (I := I) (nablaA x) (basis i))) := by
          rw [inner02_rough (I := I) g basis gInv hinv
            (A x)
            (tensor02FreezeNabla2 (I := I) (nabla2A x) (basis i) (basis j))]
          rw [inner02_symm (I := I) g x
            (tensor02FreezeNabla (I := I) (nablaA x) (basis j))
            (tensor02FreezeNabla (I := I) (nablaA x) (basis i))]
          rw [inner02_rough (I := I) g basis gInv hinv
            (tensor02FreezeNabla (I := I) (nablaA x) (basis j))
            (tensor02FreezeNabla (I := I) (nablaA x) (basis i))]





def Tensor02NormSecondProductInBasis
    {Idx : Type*} [Fintype Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (A roughA : Tensor02At (I := I) x)
    (nablaA : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (normSecond : Tensor02At (I := I) x) : Prop :=
  metricTrace0S2InBasis (I := I) basis gInv normSecond Fin.elim0 =
    (2 : Real) *
      (tensor02RoughInnerCoord (I := I) basis gInv A roughA +
        tensor02NablaNormCoord (I := I) basis gInv nablaA)

set_option maxHeartbeats 800000 in

omit [FiniteDimensional ℝ E] in
theorem Tensor02NormSecondProductInBasis.of_hessian_product
    {Idx : Type*} [Fintype Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (A roughA : Tensor02At (I := I) x)
    (nablaA : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (nabla2A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 x)
    (normSecond : Tensor02At (I := I) x)
    (hprod : Tensor02NormHessianProductInBasis (I := I) basis gInv A nablaA
      nabla2A normSecond)
    (hrough : RoughLap0SRealizesMetricTraceInBasis (I := I) basis gInv
      (s := 2) roughA nabla2A) :
    Tensor02NormSecondProductInBasis (I := I) basis gInv A roughA nablaA
      normSecond := by
  classical
  unfold Tensor02NormSecondProductInBasis metricTrace0S2InBasis
  calc
    (∑ i : Idx, ∑ j : Idx,
        gInv i j *
          normSecond (metricTraceInput (I := I) (basis i) (basis j) Fin.elim0))
        =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j * normSecond (vec2 (I := I) (basis i) (basis j)) := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          have hinput :
              metricTraceInput (I := I) (basis i) (basis j) Fin.elim0 =
                vec2 (I := I) (basis i) (basis j) := by
            funext a
            fin_cases a
            · simp [metricTraceInput, vec2, DifferentialGeometry.Integral.Connection.vec2]
            · rfl
          rw [hinput]
    _ =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j * ((2 : Real) *
          (tensor02RoughInnerCoord (I := I) basis gInv A
              (tensor02FreezeNabla2 (I := I) nabla2A (basis i) (basis j)) +
            tensor02RoughInnerCoord (I := I) basis gInv
              (tensor02FreezeNabla (I := I) nablaA (basis j))
              (tensor02FreezeNabla (I := I) nablaA (basis i)))) := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          rw [hprod i j]
    _ =
      (2 : Real) *
        (tensor02RoughInnerCoord (I := I) basis gInv A roughA +
          tensor02NablaNormCoord (I := I) basis gInv nablaA) := by
          have hrough_eval : ∀ p q : Idx,
              roughA (vec2 (I := I) (basis p) (basis q)) =
                ∑ i : Idx, ∑ j : Idx,
                  gInv i j *
                    tensor02FreezeNabla2 (I := I) nabla2A (basis i) (basis j)
                      (vec2 (I := I) (basis p) (basis q)) := by
            intro p q
            rw [hrough (vec2 (I := I) (basis p) (basis q))]
            unfold roughLap0SAt metricTrace0S2InBasis
            apply Finset.sum_congr rfl
            intro i _
            apply Finset.sum_congr rfl
            intro j _
            congr 1
            rw [tensor02FreezeNabla2_apply]
            congr 1
            exact metricTraceInput_vec2_eq_vec4 (I := I)
              (basis i) (basis j) (basis p) (basis q)
          let R : Real :=
            ∑ i : Idx, ∑ j : Idx,
              gInv i j *
                tensor02RoughInnerCoord (I := I) basis gInv A
                  (tensor02FreezeNabla2 (I := I) nabla2A (basis i) (basis j))
          let N : Real :=
            ∑ i : Idx, ∑ j : Idx,
              gInv i j *
                tensor02RoughInnerCoord (I := I) basis gInv
                  (tensor02FreezeNabla (I := I) nablaA (basis j))
                  (tensor02FreezeNabla (I := I) nablaA (basis i))
          have hR :
              R = tensor02RoughInnerCoord (I := I) basis gInv A roughA := by
            unfold R tensor02RoughInnerCoord
            simpa [hrough_eval] using
              (sum_trace_tensor02_rough
                (G := gInv)
                (A := fun k l => A (vec2 (I := I) (basis k) (basis l)))
                (B := fun a b i j =>
                  tensor02FreezeNabla2 (I := I) nabla2A (basis a) (basis b)
                    (vec2 (I := I) (basis i) (basis j))))
          have hN :
              N = tensor02NablaNormCoord (I := I) basis gInv nablaA := by
            unfold N tensor02RoughInnerCoord tensor02NablaNormCoord
            simpa [tensor02FreezeNabla_apply] using
              (sum_trace_tensor02_nabla
                (G := gInv)
                (B := fun a i j =>
                  nablaA (vec3 (I := I) (basis a) (basis i) (basis j))))
          calc
            (∑ i : Idx, ∑ j : Idx,
                gInv i j *
                  (2 *
                    (tensor02RoughInnerCoord (I := I) basis gInv A
                        (tensor02FreezeNabla2 (I := I) nabla2A (basis i) (basis j)) +
                      tensor02RoughInnerCoord (I := I) basis gInv
                        (tensor02FreezeNabla (I := I) nablaA (basis j))
                        (tensor02FreezeNabla (I := I) nablaA (basis i)))))
                = (2 : Real) * (R + N) := by
                  unfold R N
                  simp_rw [mul_add, Finset.sum_add_distrib]
                  simp [Finset.mul_sum, mul_left_comm]
    _ = (2 : Real) *
                (tensor02RoughInnerCoord (I := I) basis gInv A roughA +
                  tensor02NablaNormCoord (I := I) basis gInv nablaA) := by
                  rw [hR, hN]


theorem second_norm02_mc
    [T2Space M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    (hmc : DifferentialGeometry.Integral.Connection.IsMetricCompatible_gen (I := I) cov g)
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : Tensor0SBundle.MetricInverseInBasis_gen (I := I) (M := M) g x basis gInv)
    (X : Idx -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (hfields : SmoothBasisFieldsAt (I := I) basis X)
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2)
    (roughA : Tensor02At (I := I) x)
    (nablaA :
      Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) 3)
    (nabla2A :
      Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) 4)
    (hA : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 2 cov A nablaA)
    (h2 : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 3 cov nablaA nabla2A)
    (du : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1)
    (normSecond : (y : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 y)
    (hdu : DuFieldRealizes (I := I)
      (fun y : M => normSq02 (I := I) g y (A y)) du)
    (hHess : HessianRealizesNablaDuAt (I := I) cov du normSecond x)
    (hrough : RoughLap0SRealizesMetricTraceInBasis (I := I) basis gInv
      (s := 2) roughA (nabla2A x)) :
    Tensor02NormSecondProductInBasis (I := I) basis gInv (A x) roughA
      (nablaA x) (normSecond x) := by
  exact
    Tensor02NormSecondProductInBasis.of_hessian_product (I := I) basis gInv
      (A x) roughA (nablaA x) (nabla2A x) (normSecond x)
      (hess_norm02 (I := I) cov g hmc basis gInv hinv X hfields A
        nablaA nabla2A hA h2 du normSecond hdu hHess)
      hrough


def Tensor02NormProductRuleInBasis
    {Idx : Type*} [Fintype Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (lapNormSq : Real)
    (A roughA : Tensor02At (I := I) x)
    (nablaA : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x) :
    Prop :=
  lapNormSq =
    2 * tensor02RoughInnerCoord (I := I) basis gInv A roughA +
      2 * tensor02NablaNormCoord (I := I) basis gInv nablaA



theorem tensor02_norm_product_rule_of_second_product
    {Idx : Type*} [Fintype Idx]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (f : M -> Real)
    (A roughA : Tensor02At (I := I) x)
    (nablaA : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (normSecond : Tensor02At (I := I) x)
    (hlap :
      laplacian (I := I) cov g f x =
        metricTrace0S2InBasis (I := I) basis gInv normSecond Fin.elim0)
    (hsecond : Tensor02NormSecondProductInBasis (I := I) basis gInv A roughA
      nablaA normSecond) :
    Tensor02NormProductRuleInBasis (I := I) basis gInv
      (laplacian (I := I) cov g f x) A roughA nablaA := by
  unfold Tensor02NormProductRuleInBasis
  rw [hlap]
  unfold Tensor02NormSecondProductInBasis at hsecond
  rw [hsecond]
  ring

end Tensor02Product






def RicciNormScalarLaplacianExpansionInFrame
    (ricciNormLap : Time -> M -> Real)
    (roughLapRic : Time -> M -> Idx -> Idx -> Real)
    (Ric : Time -> RawTwoTensorField (I := I) (M := M))
    (gInv : Time -> InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (nablaRic : Time -> M -> Idx -> Idx -> Idx -> Real) : Prop :=
  forall (t : Time) (x : M),
    ricciNormLap t x =
      2 * (∑ i : Idx, ∑ j : Idx,
        roughLapRic t x i j *
          raisedRicciComponentsInFrame (I := I) Ric gInv frame t x i j) +
        2 * (∑ a : Idx, ∑ b : Idx, ∑ i : Idx, ∑ j : Idx,
          ∑ k : Idx, ∑ l : Idx,
            gInv t x a b * gInv t x i k * gInv t x j l *
              nablaRic t x a i j * nablaRic t x b k l)

section Tensor02ProductProducer

variable [FiniteDimensional Real E]







omit [FiniteDimensional ℝ E] in
theorem ricciNormScalarLaplacianExpansionInFrame_of_tensor02_product_rule
    (ricciNormLap : Time -> M -> Real)
    (roughLapRic : Time -> M -> Idx -> Idx -> Real)
    (Ric : Time -> RawTwoTensorField (I := I) (M := M))
    (gInv : Time -> InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (nablaRic : Time -> M -> Idx -> Idx -> Idx -> Real)
    (basis : (x : M) -> Module.Basis Idx Real (TangentSpace I x))
    (A roughA : Time -> (x : M) -> Tensor02At (I := I) x)
    (nablaA : Time -> (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (normSecond : Time -> (x : M) -> Tensor02At (I := I) x)
    (hframe : forall x i, basis x i = frame i x)
    (hlapTrace : forall t x,
      ricciNormLap t x =
        metricTrace0S2InBasis (I := I) (basis x) (gInv t x)
          (normSecond t x) Fin.elim0)
    (hsecond : forall t x,
      Tensor02NormSecondProductInBasis (I := I) (basis x) (gInv t x)
        (A t x) (roughA t x) (nablaA t x) (normSecond t x))
    (hAComp : forall t x i j,
      A t x (vec2 (I := I) (frame i x) (frame j x)) =
        Ric t x (frame i x) (frame j x))
    (hroughComp : forall t x i j,
      roughA t x (vec2 (I := I) (frame i x) (frame j x)) =
        roughLapRic t x i j)
    (hnablaComp : forall t x a i j,
      nablaA t x (vec3 (I := I) (frame a x) (frame i x) (frame j x)) =
        nablaRic t x a i j) :
    RicciNormScalarLaplacianExpansionInFrame
      (I := I) ricciNormLap roughLapRic Ric gInv frame nablaRic := by
  classical
  intro t x
  have hprod :
      ricciNormLap t x =
        2 * tensor02RoughInnerCoord (I := I) (basis x) (gInv t x)
            (A t x) (roughA t x) +
          2 * tensor02NablaNormCoord (I := I) (basis x) (gInv t x)
            (nablaA t x) := by
    rw [hlapTrace t x]
    rw [hsecond t x]
    ring
  have hrough :
      tensor02RoughInnerCoord (I := I) (basis x) (gInv t x)
          (A t x) (roughA t x) =
        ∑ i : Idx, ∑ j : Idx,
          roughLapRic t x i j *
            raisedRicciComponentsInFrame (I := I) Ric gInv frame t x i j := by
    unfold tensor02RoughInnerCoord raisedRicciComponentsInFrame
    simp_rw [hframe]
    simp_rw [hAComp]
    simp_rw [hroughComp]
  have hnabla :
      tensor02NablaNormCoord (I := I) (basis x) (gInv t x) (nablaA t x) =
        ∑ a : Idx, ∑ b : Idx, ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          gInv t x a b * gInv t x i k * gInv t x j l *
            nablaRic t x a i j * nablaRic t x b k l := by
    unfold tensor02NablaNormCoord
    simp_rw [hframe]
    simp_rw [hnablaComp]
  rw [hprod, hrough, hnabla]



theorem ricci_lap_mc
    [T2Space M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (G : RealizedMetricFamily (I := I) (M := M) Time)
    (ricciNormLap : Time -> M -> Real)
    (roughLapRic : Time -> M -> Idx -> Idx -> Real)
    (Ric : Time -> RawTwoTensorField (I := I) (M := M))
    (gInv : Time -> InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (nablaRic : Time -> M -> Idx -> Idx -> Idx -> Real)
    (basis : (x : M) -> Module.Basis Idx Real (TangentSpace I x))
    (X : (x : M) -> Idx -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (A : Time -> Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (roughA : Time -> (x : M) -> Tensor02At (I := I) x)
    (nablaA : Time -> Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 3)
    (nabla2A : Time -> Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 4)
    (du : Time -> Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 1)
    (normSecond : Time -> (y : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 y)
    (hframe : forall x i, basis x i = frame i x)
    (hinv : forall t x,
      Tensor0SBundle.MetricInverseInBasis_gen (I := I) (M := M) (G.metric t) x
        (basis x) (gInv t x))
    (hfields : forall x, SmoothBasisFieldsAt (I := I) (basis x) (X x))
    (hlapTrace : forall t x,
      ricciNormLap t x =
        metricTrace0S2InBasis (I := I) (basis x) (gInv t x)
          (normSecond t x) Fin.elim0)
    (hA : forall t,
      TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I)
        (M := M) 2 (G.connection t) (A t) (nablaA t))
    (h2 : forall t,
      TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I)
        (M := M) 3 (G.connection t) (nablaA t) (nabla2A t))
    (hdu : forall t,
      DuFieldRealizes (I := I)
        (fun y : M => normSq02 (I := I) (G.metric t) y (A t y)) (du t))
    (hHess : forall t x,
      HessianRealizesNablaDuAt (I := I) (G.connection t) (du t)
        (normSecond t) x)
    (hrough : forall t x,
      RoughLap0SRealizesMetricTraceInBasis (I := I) (basis x) (gInv t x)
        (s := 2) (roughA t x) (nabla2A t x))
    (hAComp : forall t x i j,
      A t x (vec2 (I := I) (frame i x) (frame j x)) =
        Ric t x (frame i x) (frame j x))
    (hroughComp : forall t x i j,
      roughA t x (vec2 (I := I) (frame i x) (frame j x)) =
        roughLapRic t x i j)
    (hnablaComp : forall t x a i j,
      nablaA t x (vec3 (I := I) (frame a x) (frame i x) (frame j x)) =
        nablaRic t x a i j) :
    RicciNormScalarLaplacianExpansionInFrame
      (I := I) ricciNormLap roughLapRic Ric gInv frame nablaRic := by
  refine
    ricciNormScalarLaplacianExpansionInFrame_of_tensor02_product_rule
      (I := I) ricciNormLap roughLapRic Ric gInv frame nablaRic basis
      (fun t x => A t x) roughA (fun t x => nablaA t x) normSecond
      hframe hlapTrace ?_ hAComp hroughComp hnablaComp
  intro t x
  exact
    second_norm02_mc (I := I) (G.connection t) (G.metric t)
      (G.metricCompatible t) (basis x) (gInv t x) (hinv t x)
      (X x) (hfields x) (A t) (roughA t x) (nablaA t) (nabla2A t)
      (hA t) (h2 t) (du t) (normSecond t) (hdu t) (hHess t x)
      (hrough t x)

end Tensor02ProductProducer




def curvRicciRicciReactionInFrame
    (Riemann04 : Time -> RawFourTensorField (I := I) (M := M))
    (RicRaised : Time -> M -> Idx -> Idx -> Real)
    (frame : Idx -> (x : M) -> TangentSpace I x) :
    Time -> M -> Real :=
  fun t x =>
    ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      Riemann04 t x (frame i x) (frame k x) (frame j x) (frame l x) *
        RicRaised t x i j * RicRaised t x k l

omit [IsManifold I ∞ M] in
@[simp] theorem curvRicciRicciReactionInFrame_apply
    (Riemann04 : Time -> RawFourTensorField (I := I) (M := M))
    (RicRaised : Time -> M -> Idx -> Idx -> Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Time) (x : M) :
    curvRicciRicciReactionInFrame (I := I) Riemann04 RicRaised frame t x =
      ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
        Riemann04 t x (frame i x) (frame k x) (frame j x) (frame l x) *
          RicRaised t x i j * RicRaised t x k l := by
  rfl





def RicciNormTimeDerivativeComponentsInFrame
    (ricciNormDt roughLapInner reaction : Time -> M -> Real) : Prop :=
  forall (t : Time) (x : M),
    ricciNormDt t x = 2 * roughLapInner t x + 4 * reaction t x



def RicciNormLaplacianComponentsInFrame
    (ricciNormLap roughLapInner nablaRicNormSq : Time -> M -> Real) : Prop :=
  forall (t : Time) (x : M),
    ricciNormLap t x = 2 * roughLapInner t x + 2 * nablaRicNormSq t x





omit [IsManifold I ∞ M] in
theorem ricciNormLaplacianComponentsInFrame_of_normSq_laplacian_expansion
    (ricciNormLap : Time -> M -> Real)
    (roughLapRic : Time -> M -> Idx -> Idx -> Real)
    (Ric : Time -> RawTwoTensorField (I := I) (M := M))
    (gInv : Time -> InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (nablaRic : Time -> M -> Idx -> Idx -> Idx -> Real)
    (h_lap : RicciNormScalarLaplacianExpansionInFrame
      (I := I) ricciNormLap roughLapRic Ric gInv frame nablaRic) :
    RicciNormLaplacianComponentsInFrame
      ricciNormLap
      (roughLapRicciInnerInFrame (I := I) roughLapRic Ric gInv frame)
      (nablaRicciNormSqInFrame (M := M) nablaRic gInv) := by
  intro t x
  rw [h_lap t x]
  rfl



omit [TopologicalSpace M] in
theorem ricci_norm_heat_eq_of_bochner_components
    (ricciNormDt ricciNormLap roughLapInner nablaRicNormSq reaction : Time -> M -> Real)
    (h_dt : RicciNormTimeDerivativeComponentsInFrame
      ricciNormDt roughLapInner reaction)
    (h_lap : RicciNormLaplacianComponentsInFrame
      ricciNormLap roughLapInner nablaRicNormSq) :
    forall (t : Time) (x : M),
      ricciNormDt t x - ricciNormLap t x =
        -2 * nablaRicNormSq t x + 4 * reaction t x := by
  intro t x
  rw [h_dt t x, h_lap t x]
  ring

end RicciNorm

end

end DifferentialGeometry.Integral.Connection
