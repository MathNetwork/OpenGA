import DifferentialGeometry.Geometry.Curvature.Realized.CurvatureTensor
import DifferentialGeometry.Geometry.Coordinates.MetricCompatibility.Inverse
import DifferentialGeometry.Geometry.Coordinates.MetricCompatibility.Covariant
import DifferentialGeometry.Geometry.Coordinates.MetricCompatibility.Coordinate
import DifferentialGeometry.Tensor.RSTensor.Tensor0SRiemannian.Basic
import DifferentialGeometry.Tensor.RSTensor.Tensor0SRiemannian.Coordinate
import DifferentialGeometry.Tensor.RSTensor.Tensor0SRiemannian.Comparison
import DifferentialGeometry.Tensor.RSTensor.Tensor0SRiemannian.Product
import DifferentialGeometry.Tensor.RSTensor.Tensor0SRiemannian.Smooth

set_option autoImplicit false
set_option linter.style.longLine false










namespace DifferentialGeometry.Integral.Connection

noncomputable section

open Bundle Tensor0SBundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]



def metricTraceInput {x : M} {s : ℕ}
    (X Y : TangentSpace I x) (tail : Fin s -> TangentSpace I x) :
    Fin (s + 2) -> TangentSpace I x :=
  Fin.cases X (Fin.cases Y tail)


def metricTensor0S (g : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x :=
  (((continuousMultilinearCurryFin1 Real (TangentSpace I x) Real).symm.toContinuousLinearMap).comp
    (g.inner x)).uncurryLeft

@[simp]
theorem metricTensor0S_apply
    (g : SmoothRiemannianMetric I M) (x : M)
    (v : Fin 2 -> TangentSpace I x) :
    metricTensor0S (I := I) g x v = g.inner x (v 0) (v 1) := by
  unfold metricTensor0S
  change
    ((continuousMultilinearCurryFin1 Real (TangentSpace I x) Real).symm
      (g.inner x (v 0))) (fun i : Fin 1 => v i.succ) =
      g.inner x (v 0) (v 1)
  have htail : (fun i : Fin 1 => v i.succ) = fun _ : Fin 1 => v 1 := by
    funext i
    fin_cases i
    rfl
  rw [htail]
  rfl






def metricTracePair0SAt (g : SmoothRiemannianMetric I M)
    {x : M}
    (B : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :
    Real :=
  inner0S (I := I) g x 2 (metricTensor0S (I := I) g x) B

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

omit [FiniteDimensional ℝ E] in
private theorem tensor0SSpace_sum_apply {ι : Type*} [Fintype ι] {x : M} {s : ℕ}
    (T : ι -> Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (v : Fin s -> TangentSpace I x) :
    ((∑ i : ι, T i) v) = ∑ i : ι, (T i) v := by
  classical
  let S : Finset ι := Finset.univ
  change ((∑ i ∈ S, T i) v) = ∑ i ∈ S, (T i) v
  induction S using Finset.induction_on with
  | empty =>
      change (0 : ContinuousMultilinearMap Real (fun _ : Fin s => E) Real) v = 0
      simp
  | insert a S ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      change T a v + (∑ i ∈ S, T i) v = T a v + ∑ i ∈ S, T i v
      rw [ih]

omit [FiniteDimensional ℝ E] in
private theorem tensor0SSpace_smul_apply {x : M} {s : ℕ}
    (c : Real)
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (v : Fin s -> TangentSpace I x) :
    (c • T) v = c * T v := by
  rfl

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
private theorem metricTraceInput_update_first {x : M} {s : ℕ}
    (v : Fin 2 -> TangentSpace I x) (tail : Fin s -> TangentSpace I x)
    (X : TangentSpace I x) :
    metricTraceInput (I := I) X (v 1) tail =
      Function.update (metricTraceInput (I := I) (v 0) (v 1) tail)
        (0 : Fin (s + 2)) X := by
  funext a
  rcases Fin.eq_zero_or_eq_succ a with h | ⟨b, rfl⟩
  · subst h
    simp [metricTraceInput, Function.update]
  · simp [metricTraceInput, Function.update]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
private theorem metricTraceInput_update_second {x : M} {s : ℕ}
    (v : Fin 2 -> TangentSpace I x) (tail : Fin s -> TangentSpace I x)
    (Y : TangentSpace I x) :
    metricTraceInput (I := I) (v 0) Y tail =
      Function.update (metricTraceInput (I := I) (v 0) (v 1) tail)
        (1 : Fin (s + 2)) Y := by
  funext a
  rcases Fin.eq_zero_or_eq_succ a with h | ⟨b, rfl⟩
  · subst h
    simp [metricTraceInput, Function.update]
  · rcases Fin.eq_zero_or_eq_succ b with hb | ⟨c, rfl⟩
    · subst hb
      exact rfl
    · have hne : (c.succ.succ : Fin (s + 2)) ≠ (1 : Fin (s + 2)) := by
        intro h
        have hv := congrArg Fin.val h
        simp at hv
      simp [metricTraceInput, Function.update, hne]





omit [FiniteDimensional ℝ E] in
theorem exists_freezeFirstTwo0S {x : M} {s : ℕ}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (tail : Fin s -> TangentSpace I x) :
    ∃ B : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x,
      ∀ X Y : TangentSpace I x,
        B (vec2 (I := I) X Y) = T (metricTraceInput (I := I) X Y tail) := by
  classical
  let Traw :
      ContinuousMultilinearMap Real (fun _ : Fin (s + 2) => TangentSpace I x) Real :=
    (tensor0SSpace_continuousLinearEquiv (I := I) (M := M) (s + 2) x) T
  let L : MultilinearMap Real (fun _ : Fin 2 => TangentSpace I x) Real :=
    { toFun := fun v => Traw (metricTraceInput (I := I) (v 0) (v 1) tail)
      map_update_add' := by
        intro _ v i X Y
        fin_cases i
        · have h :=
            Traw.map_update_add (metricTraceInput (I := I) (v 0) (v 1) tail)
              (0 : Fin (s + 2)) X Y
          rw [← metricTraceInput_update_first (I := I) v tail (X + Y),
            ← metricTraceInput_update_first (I := I) v tail X,
            ← metricTraceInput_update_first (I := I) v tail Y] at h
          simpa [Function.update] using h
        · have h :=
            Traw.map_update_add (metricTraceInput (I := I) (v 0) (v 1) tail)
              (1 : Fin (s + 2)) X Y
          rw [← metricTraceInput_update_second (I := I) v tail (X + Y),
            ← metricTraceInput_update_second (I := I) v tail X,
            ← metricTraceInput_update_second (I := I) v tail Y] at h
          simpa [Function.update] using h
      map_update_smul' := by
        intro _ v i c X
        fin_cases i
        · have h :=
            Traw.map_update_smul (metricTraceInput (I := I) (v 0) (v 1) tail)
              (0 : Fin (s + 2)) c X
          rw [← metricTraceInput_update_first (I := I) v tail (c • X),
            ← metricTraceInput_update_first (I := I) v tail X] at h
          simpa [Function.update] using h
        · have h :=
            Traw.map_update_smul (metricTraceInput (I := I) (v 0) (v 1) tail)
              (1 : Fin (s + 2)) c X
          rw [← metricTraceInput_update_second (I := I) v tail (c • X),
            ← metricTraceInput_update_second (I := I) v tail X] at h
          simpa [Function.update] using h }
  let C : Real := ‖Traw‖ * ∏ a : Fin s, ‖tail a‖
  have hbound :
      ∀ v : Fin 2 -> TangentSpace I x, ‖L v‖ ≤ C * ∏ i : Fin 2, ‖v i‖ := by
    intro v
    have hT := Traw.le_opNorm (metricTraceInput (I := I) (v 0) (v 1) tail)
    have hprod :
        (∏ a : Fin (s + 2), ‖metricTraceInput (I := I) (v 0) (v 1) tail a‖)
          = ‖v 0‖ * ‖v 1‖ * ∏ a : Fin s, ‖tail a‖ := by
      rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
      simp only [metricTraceInput, Fin.cases_zero, Fin.cases_succ]
      ring
    have hprod2 : (∏ i : Fin 2, ‖v i‖) = ‖v 0‖ * ‖v 1‖ := by
      rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
      simp
    calc
      ‖L v‖
          ≤ ‖Traw‖ * (∏ a : Fin (s + 2),
              ‖metricTraceInput (I := I) (v 0) (v 1) tail a‖) := hT
      _ = C * ∏ i : Fin 2, ‖v i‖ := by
        rw [hprod, hprod2]
        simp [C]
        ring
  let Braw : ContinuousMultilinearMap Real (fun _ : Fin 2 => TangentSpace I x) Real :=
    L.mkContinuous C hbound
  refine ⟨(tensor0SSpace_continuousLinearEquiv (I := I) (M := M) 2 x).symm
    Braw, ?_⟩
  intro X Y
  change Braw (vec2 (I := I) X Y) =
    Traw (metricTraceInput (I := I) X Y tail)
  change L (vec2 (I := I) X Y) =
    Traw (metricTraceInput (I := I) X Y tail)
  simp [L, DifferentialGeometry.Integral.Connection.vec2]


def freezeFirstTwo0S {x : M} {s : ℕ}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (tail : Fin s -> TangentSpace I x) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x :=
  Classical.choose (exists_freezeFirstTwo0S (I := I) T tail)

omit [FiniteDimensional ℝ E] in
@[simp]
theorem freezeFirstTwo0S_apply {x : M} {s : ℕ}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (tail : Fin s -> TangentSpace I x) (X Y : TangentSpace I x) :
    freezeFirstTwo0S (I := I) T tail (vec2 (I := I) X Y) =
      T (metricTraceInput (I := I) X Y tail) := by
  exact Classical.choose_spec (exists_freezeFirstTwo0S (I := I) T tail) X Y



def freezeFirstTwoArgs0S {x : M} {s : ℕ}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (X Y : TangentSpace I x) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x :=
  tensor0S_curry (I := I) (𝕜 := Real) (M := M) s x
    (tensor0S_curry (I := I) (𝕜 := Real) (M := M) (s + 1) x T X) Y

omit [FiniteDimensional ℝ E] in
@[simp]
theorem freezeFirstTwoArgs0S_apply {x : M} {s : ℕ}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (X Y : TangentSpace I x) (tail : Fin s -> TangentSpace I x) :
    freezeFirstTwoArgs0S (I := I) T X Y tail =
      T (metricTraceInput (I := I) X Y tail) := by
  unfold freezeFirstTwoArgs0S
  rw [tensor0S_curry_apply_cons_local, tensor0S_curry_apply_cons_local]
  rfl



omit [FiniteDimensional ℝ E] in
theorem exists_freezeLastTwo0S3 {x : M}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (Y : TangentSpace I x) :
    ∃ B : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x,
      ∀ X Z : TangentSpace I x,
        B (vec2 (I := I) X Z) = T (vec3 (I := I) Y X Z) := by
  refine ⟨tensor0S_curry (I := I) (𝕜 := Real) (M := M) 2 x T Y, ?_⟩
  intro X Z
  rw [tensor0S_curry_apply_cons_local]
  congr 1
  funext a
  fin_cases a
  · norm_num [DifferentialGeometry.Integral.Connection.vec2, DifferentialGeometry.Integral.Connection.vec3]
  · norm_num [DifferentialGeometry.Integral.Connection.vec2, DifferentialGeometry.Integral.Connection.vec3]
  · change (vec2 (I := I) X Z) 1 = Z
    norm_num [DifferentialGeometry.Integral.Connection.vec2]


def freezeLastTwo0S3 {x : M}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (Y : TangentSpace I x) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x :=
  Classical.choose (exists_freezeLastTwo0S3 (I := I) T Y)

omit [FiniteDimensional ℝ E] in
@[simp]
theorem freezeLastTwo0S3_apply {x : M}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (Y X Z : TangentSpace I x) :
    freezeLastTwo0S3 (I := I) T Y (vec2 (I := I) X Z) =
      T (vec3 (I := I) Y X Z) := by
  exact Classical.choose_spec (exists_freezeLastTwo0S3 (I := I) T Y) X Z


def metricTraceFirstTwo0SAt (g : SmoothRiemannianMetric I M)
    {x : M} {s : ℕ}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (tail : Fin s -> TangentSpace I x) : Real :=
  metricTracePair0SAt (I := I) g (freezeFirstTwo0S (I := I) T tail)



def metricTraceLastTwo0SAt3 (g : SmoothRiemannianMetric I M)
    {x : M}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (Y : TangentSpace I x) : Real :=
  metricTracePair0SAt (I := I) g (freezeLastTwo0S3 (I := I) T Y)




def metricTrace0S2InBasis
    {Idx : Type*} [Fintype Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real) {s : ℕ}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (tail : Fin s -> TangentSpace I x) : Real :=
  ∑ i : Idx, ∑ j : Idx,
    gInv i j * T (metricTraceInput (I := I) (basis i) (basis j) tail)


def metricTrace0S2TensorInBasis
    {Idx : Type*} [Fintype Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real) {s : ℕ}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x :=
  ∑ i : Idx, ∑ j : Idx,
    gInv i j • freezeFirstTwoArgs0S (I := I) T (basis i) (basis j)

omit [FiniteDimensional ℝ E] in
@[simp]
theorem metricTrace0S2TensorInBasis_apply
    {Idx : Type*} [Fintype Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real) {s : ℕ}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (tail : Fin s -> TangentSpace I x) :
    metricTrace0S2TensorInBasis (I := I) basis gInv T tail =
      metricTrace0S2InBasis (I := I) basis gInv T tail := by
  rw [metricTrace0S2TensorInBasis, metricTrace0S2InBasis]
  rw [tensor0SSpace_sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [tensor0SSpace_sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [tensor0SSpace_smul_apply, freezeFirstTwoArgs0S_apply]

omit [FiniteDimensional ℝ E] in
private theorem metricInverseInBasis_contract_left
    (g : SmoothRiemannianMetric I M)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis_gen (I := I) g x basis gInv)
    (j k : Idx) :
    (∑ i : Idx, gInv i k * g.inner x (basis i) (basis j)) =
      (if j = k then 1 else 0) := by
  calc
    (∑ i : Idx, gInv i k * g.inner x (basis i) (basis j))
        = ∑ i : Idx, g.inner x (basis j) (basis i) * gInv i k := by
          apply Finset.sum_congr rfl
          intro i _
          rw [g.symm x (basis i) (basis j)]
          ring
    _ = (if j = k then 1 else 0) := (hinv j k).2

omit [FiniteDimensional ℝ E] in
private theorem metricInverseInBasis_contract_metric
    (g : SmoothRiemannianMetric I M)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis_gen (I := I) g x basis gInv)
    (k l : Idx) :
    (∑ i : Idx, ∑ j : Idx,
      gInv i k * gInv j l * g.inner x (basis i) (basis j)) =
        gInv k l := by
  calc
    (∑ i : Idx, ∑ j : Idx,
      gInv i k * gInv j l * g.inner x (basis i) (basis j))
        = ∑ j : Idx,
            (∑ i : Idx, gInv i k * g.inner x (basis i) (basis j)) *
              gInv j l := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i _
          ring
    _ = ∑ j : Idx, (if j = k then 1 else 0) * gInv j l := by
          apply Finset.sum_congr rfl
          intro j _
          rw [metricInverseInBasis_contract_left (I := I) g basis gInv hinv j k]
    _ = gInv k l := by
          rw [Finset.sum_eq_single k]
          · simp
          · intro b _ hb
            simp [hb]
          · intro hk
            simp at hk


theorem metricTracePair0SAt_eq_sum_basis
    (g : SmoothRiemannianMetric I M)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis_gen (I := I) g x basis gInv)
    (B : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :
    metricTracePair0SAt (I := I) g B =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j * B (vec2 (I := I) (basis i) (basis j)) := by
  classical
  rw [metricTracePair0SAt]
  rw [inner0S_two_eq_coord_direct (I := I) g x basis gInv hinv
    (metricTensor0S (I := I) g x) B]
  simp only [metricTensor0S_apply]
  calc
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      gInv i k * gInv j l * g.inner x (basis i) (basis j) *
        B (fun a : Fin 2 => if a = 0 then basis k else basis l))
        =
      ∑ i : Idx, ∑ k : Idx, ∑ j : Idx, ∑ l : Idx,
        gInv i k * gInv j l * g.inner x (basis i) (basis j) *
          B (fun a : Fin 2 => if a = 0 then basis k else basis l) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_comm]
    _ =
      ∑ k : Idx, ∑ i : Idx, ∑ j : Idx, ∑ l : Idx,
        gInv i k * gInv j l * g.inner x (basis i) (basis j) *
          B (fun a : Fin 2 => if a = 0 then basis k else basis l) := by
          rw [Finset.sum_comm]
    _ =
      ∑ k : Idx, ∑ i : Idx, ∑ l : Idx, ∑ j : Idx,
        gInv i k * gInv j l * g.inner x (basis i) (basis j) *
          B (fun a : Fin 2 => if a = 0 then basis k else basis l) := by
          apply Finset.sum_congr rfl
          intro k _
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_comm]
    _ =
      ∑ k : Idx, ∑ l : Idx, ∑ i : Idx, ∑ j : Idx,
        gInv i k * gInv j l * g.inner x (basis i) (basis j) *
          B (fun a : Fin 2 => if a = 0 then basis k else basis l) := by
          apply Finset.sum_congr rfl
          intro k _
          rw [Finset.sum_comm]
    _ =
      ∑ k : Idx, ∑ l : Idx,
        (∑ i : Idx, ∑ j : Idx,
          gInv i k * gInv j l * g.inner x (basis i) (basis j)) *
          B (fun a : Fin 2 => if a = 0 then basis k else basis l) := by
          apply Finset.sum_congr rfl
          intro k _
          apply Finset.sum_congr rfl
          intro l _
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_mul]
    _ = ∑ k : Idx, ∑ l : Idx,
        gInv k l * B (fun a : Fin 2 => if a = 0 then basis k else basis l) := by
          apply Finset.sum_congr rfl
          intro k _
          apply Finset.sum_congr rfl
          intro l _
          rw [metricInverseInBasis_contract_metric (I := I) g basis gInv hinv k l]
    _ = ∑ k : Idx, ∑ l : Idx,
        gInv k l * B (vec2 (I := I) (basis k) (basis l)) := by
          apply Finset.sum_congr rfl
          intro k _
          apply Finset.sum_congr rfl
          intro l _
          congr 1



theorem normSq0S_metricTensor0S_eq_card
    (g : SmoothRiemannianMetric I M)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis_gen (I := I) g x basis gInv) :
    normSq0S (I := I) g x 2 (metricTensor0S (I := I) g x) =
      (Fintype.card Idx : Real) := by
  classical
  rw [normSq0S_eq_inner]
  change metricTracePair0SAt (I := I) g (metricTensor0S (I := I) g x) =
    (Fintype.card Idx : Real)
  rw [metricTracePair0SAt_eq_sum_basis (I := I) g basis gInv hinv]
  calc
    (∑ i : Idx, ∑ j : Idx,
        gInv i j * metricTensor0S (I := I) g x (vec2 (I := I) (basis i) (basis j)))
        =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j * g.inner x (basis j) (basis i) := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          simp [metricTensor0S_apply, vec2, DifferentialGeometry.Integral.Connection.vec2,
            g.symm x (basis i) (basis j)]
    _ = ∑ i : Idx, (if i = i then (1 : Real) else 0) := by
          apply Finset.sum_congr rfl
          intro i _
          exact (hinv i i).1
    _ = (Fintype.card Idx : Real) := by
          simp



theorem metricTracePair0SAt_sq_le_card_mul_normSq0S
    (g : SmoothRiemannianMetric I M)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis_gen (I := I) g x basis gInv)
    (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :
    (metricTracePair0SAt (I := I) g A) ^ 2 <=
      (Fintype.card Idx : Real) * normSq0S (I := I) g x 2 A := by
  let D := tensor0SMetricData (I := I) g x 2
  letI : PreInnerProductSpace.Core Real
      (Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :=
    D.toCore.toCore
  letI : Inner Real
      (Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :=
    D.toCore.toCore.toInner
  have hcs :=
    InnerProductSpace.Core.inner_mul_inner_self_le
      (𝕜 := Real)
      (F := Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
      (metricTensor0S (I := I) g x) A
  have hmetric :
      Inner.inner Real (metricTensor0S (I := I) g x)
          (metricTensor0S (I := I) g x) =
        (Fintype.card Idx : Real) := by
    change D.inner (metricTensor0S (I := I) g x)
        (metricTensor0S (I := I) g x) = (Fintype.card Idx : Real)
    exact normSq0S_metricTensor0S_eq_card (I := I) g basis gInv hinv
  have hA :
      Inner.inner Real A A = normSq0S (I := I) g x 2 A := by
    change D.inner A A = normSq0S (I := I) g x 2 A
    rfl
  have htrace :
      Inner.inner Real (metricTensor0S (I := I) g x) A =
        metricTracePair0SAt (I := I) g A := by
    change D.inner (metricTensor0S (I := I) g x) A =
      metricTracePair0SAt (I := I) g A
    rfl
  have htrace_comm :
      Inner.inner Real A (metricTensor0S (I := I) g x) =
        metricTracePair0SAt (I := I) g A := by
    change D.inner A (metricTensor0S (I := I) g x) =
      metricTracePair0SAt (I := I) g A
    rw [D.inner_comm]
    rfl
  have habs :
      ‖Inner.inner Real (metricTensor0S (I := I) g x) A‖ *
          ‖Inner.inner Real A (metricTensor0S (I := I) g x)‖ =
        (metricTracePair0SAt (I := I) g A) ^ 2 := by
    rw [htrace, htrace_comm]
    simp [Real.norm_eq_abs, pow_two]
  rw [habs, hmetric, hA] at hcs
  exact hcs



theorem trace_sub_le_c0
    (g h : SmoothRiemannianMetric I M) (x : M)
    {C : Real} (hC : 1 ≤ C)
    (hequiv : ∀ v : TangentSpace I x,
      C⁻¹ * g.inner x v v ≤ h.inner x v v ∧
        h.inner x v v ≤ C * g.inner x v v)
    (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 2 x) :
    |metricTracePair0SAt (I := I) h A -
        metricTracePair0SAt (I := I) g A| ≤
      (Module.finrank Real (TangentSpace I x) : Real) * C *
        Real.sqrt
          (normSq0S (I := I) g x 2
            (metricTensor0S (I := I) h x -
              metricTensor0S (I := I) g x)) *
        Real.sqrt (normSq0S (I := I) g x 2 A) := by
  classical
  obtain ⟨μ, basis, hginv, hhinv, hμ0, hμC⟩ :=
    exists_diagInv_of_equiv (I := I) g h x hC hequiv
  have hgON : ∀ i j, g.inner x (basis i) (basis j) =
      if i = j then (1 : Real) else 0 := by
    intro i j
    have hsum :
        (∑ k, identityInvMetric i k * g.inner x (basis k) (basis j)) =
          g.inner x (basis i) (basis j) := by
      rw [Finset.sum_eq_single i]
      · rw [identityInvMetric_apply_self, one_mul]
      · intro k _ hki
        rw [show identityInvMetric i k = 0 from
          diagonalInvMetric_eq_zero_of_ne hki.symm, zero_mul]
      · intro hi
        exact absurd (Finset.mem_univ i) hi
    rw [← hsum]
    exact (hginv i j).1
  have htrace_g :
      metricTracePair0SAt (I := I) g A =
        ∑ i, A (vec2 (I := I) (basis i) (basis i)) := by
    rw [metricTracePair0SAt_eq_sum_basis
      (I := I) g basis identityInvMetric hginv]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_eq_single i]
    · rw [identityInvMetric_apply_self, one_mul]
    · intro j _ hji
      rw [show identityInvMetric i j = 0 from
        diagonalInvMetric_eq_zero_of_ne hji.symm, zero_mul]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  have htrace_h :
      metricTracePair0SAt (I := I) h A =
        ∑ i, μ i * A (vec2 (I := I) (basis i) (basis i)) := by
    rw [metricTracePair0SAt_eq_sum_basis
      (I := I) h basis (diagonalInvMetric μ) hhinv]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_eq_single i]
    · rw [diagonalInvMetric_apply_self]
    · intro j _ hji
      rw [diagonalInvMetric_eq_zero_of_ne hji.symm, zero_mul]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  have hμinv (i) :
      μ i * h.inner x (basis i) (basis i) = 1 := by
    have hsum :
        (∑ k, diagonalInvMetric μ i k *
            h.inner x (basis k) (basis i)) =
          μ i * h.inner x (basis i) (basis i) := by
      rw [Finset.sum_eq_single i]
      · rw [diagonalInvMetric_apply_self]
      · intro k _ hki
        rw [diagonalInvMetric_eq_zero_of_ne hki.symm, zero_mul]
      · intro hi
        exact absurd (Finset.mem_univ i) hi
    rw [← hsum]
    simpa only [if_pos] using (hhinv i i).1
  let c0 :=
    Real.sqrt
      (normSq0S (I := I) g x 2
        (metricTensor0S (I := I) h x -
          metricTensor0S (I := I) g x))
  let a0 := Real.sqrt (normSq0S (I := I) g x 2 A)
  have hmetricComp (i) :
      |h.inner x (basis i) (basis i) - 1| ≤ c0 := by
    have hb := abs_apply_le_sqrt_normSq0S
      (I := I) g x 2 basis hgON
      (metricTensor0S (I := I) h x -
        metricTensor0S (I := I) g x)
      (vec2 (I := I) (basis i) (basis i))
    have hsub :
        (metricTensor0S (I := I) h x - metricTensor0S (I := I) g x)
            (vec2 (I := I) (basis i) (basis i)) =
          h.inner x (basis i) (basis i) - g.inner x (basis i) (basis i) := by
      rfl
    rw [hsub] at hb
    simpa [c0, metricTensor0S_apply, vec2, hgON] using hb
  have hAComp (i) :
      |A (vec2 (I := I) (basis i) (basis i))| ≤ a0 := by
    have hb := abs_apply_le_sqrt_normSq0S
      (I := I) g x 2 basis hgON A
      (vec2 (I := I) (basis i) (basis i))
    simpa [a0, vec2, hgON] using hb
  have hC0 : 0 ≤ C := le_trans zero_le_one hC
  have hμdiff (i) : |μ i - 1| ≤ C * c0 := by
    have hid :
        μ i - 1 =
          μ i * (1 - h.inner x (basis i) (basis i)) := by
      calc
        μ i - 1 =
            μ i - μ i * h.inner x (basis i) (basis i) := by
              rw [hμinv i]
        _ = μ i * (1 - h.inner x (basis i) (basis i)) := by
              ring
    rw [hid, abs_mul, abs_of_nonneg (hμ0 i), abs_sub_comm]
    exact mul_le_mul (hμC i) (hmetricComp i) (abs_nonneg _) hC0
  have htrace :
      metricTracePair0SAt (I := I) h A -
          metricTracePair0SAt (I := I) g A =
        ∑ i, (μ i - 1) * A (vec2 (I := I) (basis i) (basis i)) := by
    rw [htrace_h, htrace_g, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [htrace]
  calc
    |∑ i, (μ i - 1) * A (vec2 (I := I) (basis i) (basis i))|
        ≤ ∑ i, |(μ i - 1) *
            A (vec2 (I := I) (basis i) (basis i))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin (Module.finrank Real (TangentSpace I x)),
          C * c0 * a0 := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact mul_le_mul (hμdiff i) (hAComp i) (abs_nonneg _)
        (mul_nonneg hC0 (Real.sqrt_nonneg _))
    _ = (Module.finrank Real (TangentSpace I x) : Real) * C * c0 * a0 := by
      simp [mul_assoc]
    _ = (Module.finrank Real (TangentSpace I x) : Real) * C *
          Real.sqrt
            (normSq0S (I := I) g x 2
              (metricTensor0S (I := I) h x -
                metricTensor0S (I := I) g x)) *
          Real.sqrt (normSq0S (I := I) g x 2 A) := by
      rfl


theorem metricTracePair0SAt_sq_div_rank_le_normSq0S
    (g : SmoothRiemannianMetric I M)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] [Nonempty Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis_gen (I := I) g x basis gInv)
    (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :
    (1 / (Fintype.card Idx : Real)) *
        (metricTracePair0SAt (I := I) g A) ^ 2 <=
      normSq0S (I := I) g x 2 A := by
  classical
  have hcard : 0 < (Fintype.card Idx : Real) := by
    exact Nat.cast_pos.mpr Fintype.card_pos
  have h :=
    metricTracePair0SAt_sq_le_card_mul_normSq0S
      (I := I) g basis gInv hinv A
  have hdiv :
      (metricTracePair0SAt (I := I) g A) ^ 2 /
          (Fintype.card Idx : Real) <=
        normSq0S (I := I) g x 2 A := by
    rw [div_le_iff₀ hcard]
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  simpa [div_eq_mul_inv, one_div, mul_comm, mul_left_comm, mul_assoc] using hdiv


theorem metricTraceFirstTwo0SAt_eq_sum_basis
    (g : SmoothRiemannianMetric I M)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis_gen (I := I) g x basis gInv)
    {s : ℕ}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (tail : Fin s -> TangentSpace I x) :
    metricTraceFirstTwo0SAt (I := I) g T tail =
      metricTrace0S2InBasis (I := I) basis gInv T tail := by
  rw [metricTraceFirstTwo0SAt, metricTracePair0SAt_eq_sum_basis
    (I := I) g basis gInv hinv]
  unfold metricTrace0S2InBasis
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp



theorem metricTraceLastTwo0SAt3_eq_sum_basis
    (g : SmoothRiemannianMetric I M)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis_gen (I := I) g x basis gInv)
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (Y : TangentSpace I x) :
    metricTraceLastTwo0SAt3 (I := I) g T Y =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j * T (vec3 (I := I) Y (basis i) (basis j)) := by
  rw [metricTraceLastTwo0SAt3, metricTracePair0SAt_eq_sum_basis
    (I := I) g basis gInv hinv]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp


theorem metricTrace0S2InBasis_eq_metricTrace
    (g : SmoothRiemannianMetric I M)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis_gen (I := I) g x basis gInv)
    {s : ℕ}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (tail : Fin s -> TangentSpace I x) :
    metricTrace0S2InBasis (I := I) basis gInv T tail =
      metricTraceFirstTwo0SAt (I := I) g T tail :=
  (metricTraceFirstTwo0SAt_eq_sum_basis (I := I) g basis gInv hinv T tail).symm


theorem metricTrace0S2InBasis_eq_metricTrace0S2InBasis
    (g : SmoothRiemannianMetric I M)
    {Idx₁ Idx₂ : Type*} [Fintype Idx₁] [DecidableEq Idx₁]
    [Fintype Idx₂] [DecidableEq Idx₂]
    {x : M}
    (basis₁ : Module.Basis Idx₁ Real (TangentSpace I x))
    (gInv₁ : Idx₁ -> Idx₁ -> Real)
    (hinv₁ : MetricInverseInBasis_gen (I := I) g x basis₁ gInv₁)
    (basis₂ : Module.Basis Idx₂ Real (TangentSpace I x))
    (gInv₂ : Idx₂ -> Idx₂ -> Real)
    (hinv₂ : MetricInverseInBasis_gen (I := I) g x basis₂ gInv₂)
    {s : ℕ}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (tail : Fin s -> TangentSpace I x) :
    metricTrace0S2InBasis (I := I) basis₁ gInv₁ T tail =
      metricTrace0S2InBasis (I := I) basis₂ gInv₂ T tail := by
  rw [metricTrace0S2InBasis_eq_metricTrace (I := I) g basis₁ gInv₁ hinv₁ T tail,
    metricTrace0S2InBasis_eq_metricTrace (I := I) g basis₂ gInv₂ hinv₂ T tail]


def metricTraceFirstTwo0STensor
    (g : SmoothRiemannianMetric I M)
    {x : M} {s : ℕ}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x :=
  metricTrace0S2TensorInBasis (I := I)
    (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis (I := I) x)
    (fun k l : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E =>
      DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_component (I := I) g x k l
        (extChartAt I x x))
    T

@[simp]
theorem metricTraceFirstTwo0STensor_apply
    (g : SmoothRiemannianMetric I M)
    {x : M} {s : ℕ}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (tail : Fin s -> TangentSpace I x) :
    metricTraceFirstTwo0STensor (I := I) g T tail =
      metricTraceFirstTwo0SAt (I := I) g T tail := by
  rw [metricTraceFirstTwo0STensor, metricTrace0S2TensorInBasis_apply]
  exact metricTrace0S2InBasis_eq_metricTrace (I := I) g
    (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis (I := I) x)
    (fun k l : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E =>
      DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_component (I := I) g x k l
        (extChartAt I x x))
    (DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_metricInverseInBasis_center (I := I) g x)
    T tail


def roughLap0STensor
    (g : SmoothRiemannianMetric I M)
    {x : M} {s : ℕ}
    (nabla2A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x :=
  metricTraceFirstTwo0STensor (I := I) g nabla2A

@[simp]
theorem roughLap0STensor_apply
    (g : SmoothRiemannianMetric I M)
    {x : M} {s : ℕ}
    (nabla2A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (tail : Fin s -> TangentSpace I x) :
    roughLap0STensor (I := I) g nabla2A tail =
      metricTraceFirstTwo0SAt (I := I) g nabla2A tail := by
  exact metricTraceFirstTwo0STensor_apply (I := I) g nabla2A tail







theorem trace_smul_leibniz
    (g : SmoothRiemannianMetric I M)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis_gen (I := I) g x basis gInv)
    {s : ℕ}
    (f : Real)
    (df : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (hessF : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (nablaA : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 1) x)
    (nabla2A nabla2fA :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (s + 2) x)
    (tail : Fin s -> TangentSpace I x)
    (hleib :
      ∀ X Y : TangentSpace I x, ∀ tail : Fin s -> TangentSpace I x,
        nabla2fA (metricTraceInput (I := I) X Y tail) =
          hessF (metricTraceInput (I := I) X Y Fin.elim0) * A tail +
            df (fun _ : Fin 1 => X) * nablaA (Fin.cons Y tail) +
            df (fun _ : Fin 1 => Y) * nablaA (Fin.cons X tail) +
            f * nabla2A (metricTraceInput (I := I) X Y tail)) :
    metricTraceFirstTwo0SAt (I := I) g nabla2fA tail =
      metricTraceFirstTwo0SAt (I := I) g hessF Fin.elim0 * A tail +
        (∑ i : Idx, ∑ j : Idx,
          gInv i j *
            (df (fun _ : Fin 1 => basis i) *
                nablaA (Fin.cons (basis j) tail) +
              df (fun _ : Fin 1 => basis j) *
                nablaA (Fin.cons (basis i) tail))) +
        f * metricTraceFirstTwo0SAt (I := I) g nabla2A tail := by
  rw [metricTraceFirstTwo0SAt_eq_sum_basis (I := I) g basis gInv hinv
      nabla2fA tail,
    metricTraceFirstTwo0SAt_eq_sum_basis (I := I) g basis gInv hinv
      hessF Fin.elim0,
    metricTraceFirstTwo0SAt_eq_sum_basis (I := I) g basis gInv hinv
      nabla2A tail]
  simp only [metricTrace0S2InBasis]
  simp_rw [hleib]
  simp_rw [mul_add]
  simp_rw [Finset.sum_add_distrib]
  simp_rw [Finset.mul_sum]
  ring_nf
  rw [Finset.mul_sum]
  simp_rw [Finset.mul_sum]
  ring_nf




theorem trace_smul_parallel
    (g : SmoothRiemannianMetric I M)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis_gen (I := I) g x basis gInv)
    {s : ℕ}
    (f : Real)
    (df : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (hessF : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (nablaA : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 1) x)
    (nabla2A nabla2fA :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (s + 2) x)
    (tail : Fin s -> TangentSpace I x)
    (hfirst : ∀ X : TangentSpace I x, ∀ tail : Fin s -> TangentSpace I x,
      nablaA (Fin.cons X tail) = 0)
    (hsecond : ∀ X Y : TangentSpace I x, ∀ tail : Fin s -> TangentSpace I x,
      nabla2A (metricTraceInput (I := I) X Y tail) = 0)
    (hleib :
      ∀ X Y : TangentSpace I x, ∀ tail : Fin s -> TangentSpace I x,
        nabla2fA (metricTraceInput (I := I) X Y tail) =
          hessF (metricTraceInput (I := I) X Y Fin.elim0) * A tail +
            df (fun _ : Fin 1 => X) * nablaA (Fin.cons Y tail) +
            df (fun _ : Fin 1 => Y) * nablaA (Fin.cons X tail) +
            f * nabla2A (metricTraceInput (I := I) X Y tail)) :
    metricTraceFirstTwo0SAt (I := I) g nabla2fA tail =
      metricTraceFirstTwo0SAt (I := I) g hessF Fin.elim0 * A tail := by
  rw [trace_smul_leibniz (I := I) g basis gInv hinv f
    df hessF A nablaA nabla2A nabla2fA tail hleib]
  simp only [hfirst, mul_zero, add_zero]
  rw [metricTraceFirstTwo0SAt_eq_sum_basis (I := I) g basis gInv hinv
      nabla2A tail]
  simp only [metricTrace0S2InBasis, hsecond, mul_zero, Finset.sum_const_zero]
  ring


theorem roughLap_smul_leib
    (g : SmoothRiemannianMetric I M)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis_gen (I := I) g x basis gInv)
    {s : ℕ}
    (f : Real)
    (df : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (hessF : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (nablaA : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 1) x)
    (nabla2A nabla2fA :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (s + 2) x)
    (tail : Fin s -> TangentSpace I x)
    (hleib :
      ∀ X Y : TangentSpace I x, ∀ tail : Fin s -> TangentSpace I x,
        nabla2fA (metricTraceInput (I := I) X Y tail) =
          hessF (metricTraceInput (I := I) X Y Fin.elim0) * A tail +
            df (fun _ : Fin 1 => X) * nablaA (Fin.cons Y tail) +
            df (fun _ : Fin 1 => Y) * nablaA (Fin.cons X tail) +
            f * nabla2A (metricTraceInput (I := I) X Y tail)) :
    roughLap0STensor (I := I) g nabla2fA tail =
      metricTraceFirstTwo0SAt (I := I) g hessF Fin.elim0 * A tail +
        (∑ i : Idx, ∑ j : Idx,
          gInv i j *
            (df (fun _ : Fin 1 => basis i) *
                nablaA (Fin.cons (basis j) tail) +
              df (fun _ : Fin 1 => basis j) *
                nablaA (Fin.cons (basis i) tail))) +
        f * roughLap0STensor (I := I) g nabla2A tail := by
  rw [roughLap0STensor_apply, roughLap0STensor_apply]
  exact trace_smul_leibniz (I := I) g basis gInv hinv
    f df hessF A nablaA nabla2A nabla2fA tail hleib



theorem roughLap_smul_par
    (g : SmoothRiemannianMetric I M)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis_gen (I := I) g x basis gInv)
    {s : ℕ}
    (f : Real)
    (df : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (hessF : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (nablaA : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 1) x)
    (nabla2A nabla2fA :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (s + 2) x)
    (tail : Fin s -> TangentSpace I x)
    (hfirst : ∀ X : TangentSpace I x, ∀ tail : Fin s -> TangentSpace I x,
      nablaA (Fin.cons X tail) = 0)
    (hsecond : ∀ X Y : TangentSpace I x, ∀ tail : Fin s -> TangentSpace I x,
      nabla2A (metricTraceInput (I := I) X Y tail) = 0)
    (hleib :
      ∀ X Y : TangentSpace I x, ∀ tail : Fin s -> TangentSpace I x,
        nabla2fA (metricTraceInput (I := I) X Y tail) =
          hessF (metricTraceInput (I := I) X Y Fin.elim0) * A tail +
            df (fun _ : Fin 1 => X) * nablaA (Fin.cons Y tail) +
            df (fun _ : Fin 1 => Y) * nablaA (Fin.cons X tail) +
            f * nabla2A (metricTraceInput (I := I) X Y tail)) :
    roughLap0STensor (I := I) g nabla2fA tail =
      metricTraceFirstTwo0SAt (I := I) g hessF Fin.elim0 * A tail := by
  rw [roughLap0STensor_apply]
  exact trace_smul_parallel (I := I) g basis gInv hinv
    f df hessF A nablaA nabla2A nabla2fA tail hfirst hsecond hleib



def roughLap0SAt
    {Idx : Type*} [Fintype Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real) {s : ℕ}
    (nabla2A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (tail : Fin s -> TangentSpace I x) : Real :=
  metricTrace0S2InBasis (I := I) basis gInv nabla2A tail


def roughLap1FormAt
    {Idx : Type*} [Fintype Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (nabla2α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      3 x)
    (Y : TangentSpace I x) : Real :=
  roughLap0SAt (I := I) basis gInv (s := 1) nabla2α (fun _ : Fin 1 => Y)





def RoughLap0SRealizesMetricTraceInBasis
    {Idx : Type*} [Fintype Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real) {s : ℕ}
    (roughA : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (nabla2A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x) : Prop :=
  ∀ tail : Fin s -> TangentSpace I x,
    roughA tail = roughLap0SAt (I := I) basis gInv nabla2A tail

omit [FiniteDimensional ℝ E] in
theorem roughLap0SAt_eq_of_realizes
    {Idx : Type*} [Fintype Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real) {s : ℕ}
    (roughA : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (nabla2A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (h : RoughLap0SRealizesMetricTraceInBasis (I := I) basis gInv roughA nabla2A)
    (tail : Fin s -> TangentSpace I x) :
    roughA tail = roughLap0SAt (I := I) basis gInv nabla2A tail :=
  h tail

omit [FiniteDimensional ℝ E] in
theorem roughLap1FormAt_eq_of_realizes
    {Idx : Type*} [Fintype Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (roughα : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (nabla2α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (h : RoughLap0SRealizesMetricTraceInBasis (I := I) basis gInv (s := 1) roughα nabla2α)
    (Y : TangentSpace I x) :
    roughα (fun _ : Fin 1 => Y) =
      roughLap1FormAt (I := I) basis gInv nabla2α Y :=
  h (fun _ : Fin 1 => Y)











def metric_trace_0s
    (g : SmoothRiemannianMetric I M)
    {x : M} {s : ℕ}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (traceT : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      s x) : Prop :=
  ∀ tail : Fin s -> TangentSpace I x,
    traceT tail = metricTraceFirstTwo0SAt (I := I) g T tail


def RoughLap0SRealizesMetricTrace
    (g : SmoothRiemannianMetric I M)
    {x : M} {s : ℕ}
    (roughA : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      s x)
    (nabla2A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x) : Prop :=
  metric_trace_0s (I := I) g nabla2A roughA


def rough_lap_0s
    (g : SmoothRiemannianMetric I M)
    {x : M} {s : ℕ}
    (nabla2A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (roughA : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      s x) : Prop :=
  RoughLap0SRealizesMetricTrace (I := I) g roughA nabla2A

theorem metric_trace_0s_iff_eq_tensor
    (g : SmoothRiemannianMetric I M)
    {x : M} {s : ℕ}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (traceT : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      s x) :
    metric_trace_0s (I := I) g T traceT ↔
      traceT = metricTraceFirstTwo0STensor (I := I) g T := by
  constructor
  · intro htrace
    ext tail
    rw [htrace tail, metricTraceFirstTwo0STensor_apply]
  · intro htrace tail
    rw [htrace, metricTraceFirstTwo0STensor_apply]

theorem rough_lap_0s_iff_eq_tensor
    (g : SmoothRiemannianMetric I M)
    {x : M} {s : ℕ}
    (nabla2A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (roughA : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      s x) :
    rough_lap_0s (I := I) g nabla2A roughA ↔
      roughA = roughLap0STensor (I := I) g nabla2A := by
  simpa [rough_lap_0s, RoughLap0SRealizesMetricTrace, roughLap0STensor] using
    metric_trace_0s_iff_eq_tensor (I := I) g nabla2A roughA

theorem roughLap0STensor_realizes
    (g : SmoothRiemannianMetric I M)
    {x : M} {s : ℕ}
    (nabla2A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x) :
    rough_lap_0s (I := I) g nabla2A
      (roughLap0STensor (I := I) g nabla2A) := by
  rw [rough_lap_0s_iff_eq_tensor]



























def rough_lap_one_form
    (g : SmoothRiemannianMetric I M)
    {x : M}
    (nabla2α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      3 x)
    (roughα : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      1 x) : Prop :=
  rough_lap_0s (I := I) g (s := 1) nabla2α roughα

theorem metric_trace_0s_apply_basis
    (g : SmoothRiemannianMetric I M)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : M} {s : ℕ}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (traceT : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      s x)
    (htrace : metric_trace_0s (I := I) g T traceT)
    (hinv : MetricInverseInBasis_gen (I := I) g x basis gInv)
    (tail : Fin s -> TangentSpace I x) :
    traceT tail = metricTrace0S2InBasis (I := I) basis gInv T tail :=
  by
    rw [htrace tail]
    exact (metricTrace0S2InBasis_eq_metricTrace (I := I) g basis gInv hinv T tail).symm

theorem rough_lap_0s_apply_basis
    (g : SmoothRiemannianMetric I M)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : M} {s : ℕ}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (nabla2A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (roughA : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      s x)
    (hrough : rough_lap_0s (I := I) g nabla2A roughA)
    (hinv : MetricInverseInBasis_gen (I := I) g x basis gInv)
    (tail : Fin s -> TangentSpace I x) :
    roughA tail = roughLap0SAt (I := I) basis gInv nabla2A tail :=
  by
    simpa [rough_lap_0s, roughLap0SAt] using
      metric_trace_0s_apply_basis (I := I) g basis gInv nabla2A roughA hrough hinv tail

theorem rough_lap_one_form_apply_basis
    (g : SmoothRiemannianMetric I M)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (nabla2α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      3 x)
    (roughα : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      1 x)
    (hrough : rough_lap_one_form (I := I) g nabla2α roughα)
    (hinv : MetricInverseInBasis_gen (I := I) g x basis gInv)
    (Y : TangentSpace I x) :
    roughα (fun _ : Fin 1 => Y) =
      roughLap1FormAt (I := I) basis gInv nabla2α Y :=
  by
    simpa [rough_lap_one_form, rough_lap_0s, roughLap1FormAt, roughLap0SAt] using
      rough_lap_0s_apply_basis (I := I) g basis gInv nabla2α roughα hrough hinv
        (fun _ : Fin 1 => Y)



theorem rough_lap_one_form_realizes_metric_trace
    (g : SmoothRiemannianMetric I M)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (nabla2α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      3 x)
    (roughα : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      1 x)
    (hrough : rough_lap_one_form (I := I) g nabla2α roughα)
    (hinv : MetricInverseInBasis_gen (I := I) g x basis gInv) :
    RoughLap0SRealizesMetricTraceInBasis (I := I) basis gInv
      (s := 1) roughα nabla2α := by
  intro tail
  simpa [rough_lap_one_form, rough_lap_0s, roughLap0SAt] using
    rough_lap_0s_apply_basis (I := I) g basis gInv nabla2α roughα hrough hinv tail

end

end DifferentialGeometry.Integral.Connection
