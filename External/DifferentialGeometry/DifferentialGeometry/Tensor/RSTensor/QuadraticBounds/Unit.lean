import DifferentialGeometry.Geometry.Metric.MetricBallMonotone
import DifferentialGeometry.Geometry.Metric.Basic
import DifferentialGeometry.Tensor.RSTensor.Defs
import DifferentialGeometry.Tensor.Multilinear.Fiber
import DifferentialGeometry.Tensor.Multilinear.Bundle
import DifferentialGeometry.Tensor.Alternating.Comp
import DifferentialGeometry.Tensor.Multilinear.Comp
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional
import DifferentialGeometry.Tensor.Auxiliary.LinearIsometryContDiff
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Data.Bundle
import DifferentialGeometry.Tensor.Multilinear.Basis
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Topology.Algebra.Module.FiniteDimension
import DifferentialGeometry.Tensor.Multilinear.Curry
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import DifferentialGeometry.Tensor.RSTensor.Field
import DifferentialGeometry.Tensor.Multilinear.BundleSmoothEvalRealized
import Mathlib.Analysis.Normed.Module.FiniteDimension

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.longLine false







noncomputable section

namespace DifferentialGeometry

open Bundle Tensor0SBundle Set
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M]

def MetricUnitTangent (g : SmoothRiemannianMetric I M) : Type _ :=
  {p : TangentBundle I M // g.inner p.proj p.2 p.2 = 1}

instance metricUnitTop (g : SmoothRiemannianMetric I M) :
    TopologicalSpace (MetricUnitTangent (I := I) (M := M) g) :=
  inferInstanceAs (TopologicalSpace
    {p : TangentBundle I M // g.inner p.proj p.2 p.2 = 1})

namespace MetricUnitTangent


def base {g : SmoothRiemannianMetric I M}
    (p : MetricUnitTangent (I := I) (M := M) g) : M :=
  (p.1).proj


def vec {g : SmoothRiemannianMetric I M}
    (p : MetricUnitTangent (I := I) (M := M) g) :
    TangentSpace I (base (I := I) (M := M) p) :=
  (p.1).2

omit [FiniteDimensional ℝ E] [IsManifold I 1 M] in
@[simp]
theorem unit {g : SmoothRiemannianMetric I M}
    (p : MetricUnitTangent (I := I) (M := M) g) :
    g.inner (base (I := I) (M := M) p)
      (vec (I := I) (M := M) p) (vec (I := I) (M := M) p) = 1 :=
  p.2

omit [FiniteDimensional ℝ E] [IsManifold I 1 M] in
@[simp]
theorem base_mk {g : SmoothRiemannianMetric I M} {x : M}
    {v : TangentSpace I x} {hunit : g.inner x v v = 1} :
    base (I := I) (M := M)
      (⟨(⟨x, v⟩ : TangentBundle I M), hunit⟩ :
        MetricUnitTangent (I := I) (M := M) g) = x :=
  rfl

omit [FiniteDimensional ℝ E] [IsManifold I 1 M] in
@[simp]
theorem vec_mk {g : SmoothRiemannianMetric I M} {x : M}
    {v : TangentSpace I x} {hunit : g.inner x v v = 1} :
    vec (I := I) (M := M)
      (⟨(⟨x, v⟩ : TangentBundle I M), hunit⟩ :
        MetricUnitTangent (I := I) (M := M) g) = v :=
  rfl

end MetricUnitTangent


def MetricUnitTangentSlab
    (G : Real -> SmoothRiemannianMetric I M) (t0 t1 : Real) : Type _ :=
  Σ t : {t : Real // t ∈ Set.Icc t0 t1}, MetricUnitTangent (I := I) (M := M) (G t.1)

instance metricUnitTangentSlabTop
    (G : Real -> SmoothRiemannianMetric I M) (t0 t1 : Real) :
    TopologicalSpace (MetricUnitTangentSlab (I := I) (M := M) G t0 t1) :=
  inferInstanceAs (TopologicalSpace
    (Σ t : {t : Real // t ∈ Set.Icc t0 t1},
      MetricUnitTangent (I := I) (M := M) (G t.1)))




def MetricUnitTangentTimeSlab
    (G : Real -> SmoothRiemannianMetric I M) (K : Set Real) : Type _ :=
  {q : ({t : Real // t ∈ K} × TangentBundle I M) //
    (G q.1.1).inner q.2.proj q.2.2 q.2.2 = 1}

instance metricUnitTangentTimeSlabTop
    (G : Real -> SmoothRiemannianMetric I M) (K : Set Real) :
    TopologicalSpace (MetricUnitTangentTimeSlab (I := I) (M := M) G K) :=
  inferInstanceAs (TopologicalSpace
    {q : ({t : Real // t ∈ K} × TangentBundle I M) //
      (G q.1.1).inner q.2.proj q.2.2 q.2.2 = 1})


abbrev MetricUnitTangentIccSlab
    (G : Real -> SmoothRiemannianMetric I M) (t0 t1 : Real) : Type _ :=
  MetricUnitTangentTimeSlab (I := I) (M := M) G (Set.Icc t0 t1)

namespace MetricUnitTangentTimeSlab


def time {G : Real -> SmoothRiemannianMetric I M} {K : Set Real}
    (q : MetricUnitTangentTimeSlab (I := I) (M := M) G K) : Real :=
  q.1.1.1

omit [FiniteDimensional ℝ E] [IsManifold I 1 M] in
@[simp]
theorem time_mem {G : Real -> SmoothRiemannianMetric I M} {K : Set Real}
    (q : MetricUnitTangentTimeSlab (I := I) (M := M) G K) :
    time (I := I) (M := M) q ∈ K :=
  q.1.1.2


def bundlePoint {G : Real -> SmoothRiemannianMetric I M} {K : Set Real}
    (q : MetricUnitTangentTimeSlab (I := I) (M := M) G K) :
    TangentBundle I M :=
  q.1.2


def base {G : Real -> SmoothRiemannianMetric I M} {K : Set Real}
    (q : MetricUnitTangentTimeSlab (I := I) (M := M) G K) : M :=
  (bundlePoint (I := I) (M := M) q).proj


def vec {G : Real -> SmoothRiemannianMetric I M} {K : Set Real}
    (q : MetricUnitTangentTimeSlab (I := I) (M := M) G K) :
    TangentSpace I (base (I := I) (M := M) q) :=
  (bundlePoint (I := I) (M := M) q).2

omit [FiniteDimensional ℝ E] [IsManifold I 1 M] in
@[simp]
theorem unit {G : Real -> SmoothRiemannianMetric I M} {K : Set Real}
    (q : MetricUnitTangentTimeSlab (I := I) (M := M) G K) :
    (G (time (I := I) (M := M) q)).inner
      (base (I := I) (M := M) q)
      (vec (I := I) (M := M) q) (vec (I := I) (M := M) q) = 1 :=
  q.2

omit [FiniteDimensional ℝ E] [IsManifold I 1 M] in
@[simp]
theorem time_mk {G : Real -> SmoothRiemannianMetric I M} {K : Set Real}
    {t : Real} {ht : t ∈ K} {x : M} {v : TangentSpace I x}
    {hunit : (G t).inner x v v = 1} :
    time (I := I) (M := M)
      (⟨(⟨t, ht⟩, (⟨x, v⟩ : TangentBundle I M)), hunit⟩ :
        MetricUnitTangentTimeSlab (I := I) (M := M) G K) = t :=
  rfl

omit [FiniteDimensional ℝ E] [IsManifold I 1 M] in
@[simp]
theorem bundlePoint_mk {G : Real -> SmoothRiemannianMetric I M} {K : Set Real}
    {t : Real} {ht : t ∈ K} {x : M} {v : TangentSpace I x}
    {hunit : (G t).inner x v v = 1} :
    bundlePoint (I := I) (M := M)
      (⟨(⟨t, ht⟩, (⟨x, v⟩ : TangentBundle I M)), hunit⟩ :
        MetricUnitTangentTimeSlab (I := I) (M := M) G K) =
      (⟨x, v⟩ : TangentBundle I M) :=
  rfl

omit [FiniteDimensional ℝ E] [IsManifold I 1 M] in
@[simp]
theorem base_mk {G : Real -> SmoothRiemannianMetric I M} {K : Set Real}
    {t : Real} {ht : t ∈ K} {x : M} {v : TangentSpace I x}
    {hunit : (G t).inner x v v = 1} :
    base (I := I) (M := M)
      (⟨(⟨t, ht⟩, (⟨x, v⟩ : TangentBundle I M)), hunit⟩ :
        MetricUnitTangentTimeSlab (I := I) (M := M) G K) = x :=
  rfl

omit [FiniteDimensional ℝ E] [IsManifold I 1 M] in
@[simp]
theorem vec_mk {G : Real -> SmoothRiemannianMetric I M} {K : Set Real}
    {t : Real} {ht : t ∈ K} {x : M} {v : TangentSpace I x}
    {hunit : (G t).inner x v v = 1} :
    vec (I := I) (M := M)
      (⟨(⟨t, ht⟩, (⟨x, v⟩ : TangentBundle I M)), hunit⟩ :
        MetricUnitTangentTimeSlab (I := I) (M := M) G K) = v :=
  rfl

end MetricUnitTangentTimeSlab


def quad02
    {x : M}
    (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (v : TangentSpace I x) : Real :=
  A (fun _ : Fin 2 => v)


def eval02
    {x : M}
    (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (v w : TangentSpace I x) : Real :=
  A (fun i : Fin 2 => if i = 0 then v else w)

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
@[simp] theorem eval02_self
    {x : M}
    (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (v : TangentSpace I x) :
    eval02 (I := I) (M := M) A v v = quad02 (I := I) (M := M) A v := by
  unfold eval02 quad02
  congr 1
  funext i
  by_cases hi : i = 0
  · simp [hi]
  · simp [hi]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
private theorem eval02_slots_eq
    {x : M}
    (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (m : Fin 2 -> TangentSpace I x) (v w : TangentSpace I x)
    (h0 : m 0 = v) (h1 : m 1 = w) :
    A m = eval02 (I := I) (M := M) A v w := by
  congr 1
  funext i
  fin_cases i <;> simp [h0, h1]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
private theorem quad02_add_smul_eq
    {x : M}
    (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    {v w : TangentSpace I x} {a : Real}
    (hsym : eval02 (I := I) (M := M) A w v =
      eval02 (I := I) (M := M) A v w) :
    quad02 (I := I) (M := M) A (v + a • w) =
      quad02 (I := I) (M := M) A v +
        2 * a * eval02 (I := I) (M := M) A v w +
        a * a * quad02 (I := I) (M := M) A w := by
  let m : Fin 2 -> TangentSpace I x := fun _ => v + a • w
  have h0 := A.map_update_add m (0 : Fin 2) v (a • w)
  have h00 :
      Function.update m (0 : Fin 2) (v + a • w) = m := by
    funext i
    fin_cases i <;> simp [m]
  have h0v :
      A (Function.update m (0 : Fin 2) v) =
        eval02 (I := I) (M := M) A v (v + a • w) := by
    apply eval02_slots_eq
    · simp [m]
    · simp [m]
  have h0w :
      A (Function.update m (0 : Fin 2) (a • w)) =
        a * eval02 (I := I) (M := M) A w (v + a • w) := by
    have hsmul := A.map_update_smul m (0 : Fin 2) a w
    have hslot :
        A (Function.update m (0 : Fin 2) w) =
          eval02 (I := I) (M := M) A w (v + a • w) := by
      apply eval02_slots_eq
      · simp [m]
      · simp [m]
    calc
      A (Function.update m (0 : Fin 2) (a • w))
          = a • A (Function.update m (0 : Fin 2) w) := by
              exact hsmul
      _ = a * eval02 (I := I) (M := M) A w (v + a • w) := by
              simp [hslot, smul_eq_mul]
  have hfirst :
      quad02 (I := I) (M := M) A (v + a • w) =
        eval02 (I := I) (M := M) A v (v + a • w) +
          a * eval02 (I := I) (M := M) A w (v + a • w) := by
    calc
      quad02 (I := I) (M := M) A (v + a • w) = A m := by
        rfl
      _ = A (Function.update m (0 : Fin 2) (v + a • w)) := by rw [h00]
      _ = A (Function.update m (0 : Fin 2) v) +
            A (Function.update m (0 : Fin 2) (a • w)) := by
              exact h0
      _ = eval02 (I := I) (M := M) A v (v + a • w) +
            a * eval02 (I := I) (M := M) A w (v + a • w) := by
              rw [h0v, h0w]
  have hv_add :
      eval02 (I := I) (M := M) A v (v + a • w) =
        quad02 (I := I) (M := M) A v +
          a * eval02 (I := I) (M := M) A v w := by
    let mv : Fin 2 -> TangentSpace I x := fun i => if i = 0 then v else v + a • w
    have hslot :
        mv = Function.update mv (1 : Fin 2) (v + a • w) := by
      funext i
      fin_cases i <;> simp [mv]
    have hadd := A.map_update_add mv (1 : Fin 2) v (a • w)
    have hleft :
        A (Function.update mv (1 : Fin 2) (v + a • w)) =
          eval02 (I := I) (M := M) A v (v + a • w) := by
      apply eval02_slots_eq <;> simp [mv]
    have hvv :
        A (Function.update mv (1 : Fin 2) v) =
          quad02 (I := I) (M := M) A v := by
      calc
        A (Function.update mv (1 : Fin 2) v) =
            eval02 (I := I) (M := M) A v v := by
              apply eval02_slots_eq <;> simp [mv]
        _ = quad02 (I := I) (M := M) A v := by
              rw [eval02_self]
    have hvw_smul :
        A (Function.update mv (1 : Fin 2) (a • w)) =
          a * eval02 (I := I) (M := M) A v w := by
      have hsmul := A.map_update_smul mv (1 : Fin 2) a w
      have hvw :
          A (Function.update mv (1 : Fin 2) w) =
            eval02 (I := I) (M := M) A v w := by
        apply eval02_slots_eq <;> simp [mv]
      calc
        A (Function.update mv (1 : Fin 2) (a • w))
            = a • A (Function.update mv (1 : Fin 2) w) := by
                exact hsmul
        _ = a * eval02 (I := I) (M := M) A v w := by
                simp [hvw, smul_eq_mul]
    calc
      eval02 (I := I) (M := M) A v (v + a • w)
          = A (Function.update mv (1 : Fin 2) (v + a • w)) := by
              rw [hleft]
      _ = A (Function.update mv (1 : Fin 2) v) +
            A (Function.update mv (1 : Fin 2) (a • w)) := by
              exact hadd
      _ = quad02 (I := I) (M := M) A v +
            a * eval02 (I := I) (M := M) A v w := by
              rw [hvv, hvw_smul]
  have hw_add :
      eval02 (I := I) (M := M) A w (v + a • w) =
        eval02 (I := I) (M := M) A w v +
          a * quad02 (I := I) (M := M) A w := by
    let mw : Fin 2 -> TangentSpace I x := fun i => if i = 0 then w else v + a • w
    have hadd := A.map_update_add mw (1 : Fin 2) v (a • w)
    have hleft :
        A (Function.update mw (1 : Fin 2) (v + a • w)) =
          eval02 (I := I) (M := M) A w (v + a • w) := by
      apply eval02_slots_eq <;> simp [mw]
    have hwv :
        A (Function.update mw (1 : Fin 2) v) =
          eval02 (I := I) (M := M) A w v := by
      apply eval02_slots_eq <;> simp [mw]
    have hww_smul :
        A (Function.update mw (1 : Fin 2) (a • w)) =
          a * quad02 (I := I) (M := M) A w := by
      have hsmul := A.map_update_smul mw (1 : Fin 2) a w
      have hww :
          A (Function.update mw (1 : Fin 2) w) =
            quad02 (I := I) (M := M) A w := by
        calc
          A (Function.update mw (1 : Fin 2) w) =
              eval02 (I := I) (M := M) A w w := by
                apply eval02_slots_eq <;> simp [mw]
          _ = quad02 (I := I) (M := M) A w := by
                rw [eval02_self]
      calc
        A (Function.update mw (1 : Fin 2) (a • w))
            = a • A (Function.update mw (1 : Fin 2) w) := by
                exact hsmul
        _ = a * quad02 (I := I) (M := M) A w := by
                simp [hww, smul_eq_mul]
    calc
      eval02 (I := I) (M := M) A w (v + a • w)
          = A (Function.update mw (1 : Fin 2) (v + a • w)) := by
              rw [hleft]
      _ = A (Function.update mw (1 : Fin 2) v) +
            A (Function.update mw (1 : Fin 2) (a • w)) := by
              exact hadd
      _ = eval02 (I := I) (M := M) A w v +
            a * quad02 (I := I) (M := M) A w := by
              rw [hwv, hww_smul]
  calc
    quad02 (I := I) (M := M) A (v + a • w)
        = eval02 (I := I) (M := M) A v (v + a • w) +
            a * eval02 (I := I) (M := M) A w (v + a • w) := hfirst
    _ = quad02 (I := I) (M := M) A v +
          2 * a * eval02 (I := I) (M := M) A v w +
          a * a * quad02 (I := I) (M := M) A w := by
            rw [hv_add, hw_add, hsym]
            ring



omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem psd_null_left
    {x : M}
    (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    {v : TangentSpace I x}
    (hsym : ∀ u w : TangentSpace I x,
      eval02 (I := I) (M := M) A u w = eval02 (I := I) (M := M) A w u)
    (hpsd : ∀ u : TangentSpace I x, 0 ≤ quad02 (I := I) (M := M) A u)
    (hnull : quad02 (I := I) (M := M) A v = 0) :
    ∀ w : TangentSpace I x, eval02 (I := I) (M := M) A v w = 0 := by
  intro w
  let c : Real := eval02 (I := I) (M := M) A v w
  let q : Real := quad02 (I := I) (M := M) A w
  have hq : 0 ≤ q := hpsd w
  by_contra hc
  let a : Real := -c / (q + 1)
  have hden_pos : 0 < q + 1 := by linarith
  have hden_ne : q + 1 ≠ 0 := ne_of_gt hden_pos
  have hpos := hpsd (v + a • w)
  have hquad :
      quad02 (I := I) (M := M) A (v + a • w) =
        2 * a * c + a * a * q := by
    have h := quad02_add_smul_eq (I := I) (M := M) A
      (v := v) (w := w) (a := a) (hsym w v)
    simpa [c, q, hnull, add_assoc, add_comm, add_left_comm] using h
  have hnonneg : 0 ≤ 2 * a * c + a * a * q := by
    simpa [hquad] using hpos
  have hcalc : 2 * a * c + a * a * q =
      - (c * c) * (q + 2) / ((q + 1) * (q + 1)) := by
    subst a
    field_simp [hden_ne]
    ring
  have hc_sq_pos : 0 < c * c := mul_self_pos.mpr hc
  have hq2_pos : 0 < q + 2 := by linarith
  have hden_sq_pos : 0 < (q + 1) * (q + 1) := mul_pos hden_pos hden_pos
  have hneg : - (c * c) * (q + 2) / ((q + 1) * (q + 1)) < 0 := by
    exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (neg_lt_zero.mpr hc_sq_pos) hq2_pos)
      hden_sq_pos
  exact not_le_of_gt (by simpa [hcalc] using hneg) hnonneg


omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem psd_null_right
    {x : M}
    (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    {v : TangentSpace I x}
    (hsym : ∀ u w : TangentSpace I x,
      eval02 (I := I) (M := M) A u w = eval02 (I := I) (M := M) A w u)
    (hpsd : ∀ u : TangentSpace I x, 0 ≤ quad02 (I := I) (M := M) A u)
    (hnull : quad02 (I := I) (M := M) A v = 0) :
    ∀ w : TangentSpace I x, eval02 (I := I) (M := M) A w v = 0 := by
  intro w
  rw [← hsym v w]
  exact psd_null_left (I := I) (M := M) A hsym hpsd hnull w










omit [FiniteDimensional ℝ E] in
theorem metricQuad_cont
    (g : SmoothRiemannianMetric I M) :
    Continuous (fun p : TangentBundle I M => g.inner p.proj p.2 p.2) := by
  have hmetric : Continuous (fun p : TangentBundle I M =>
      TotalSpace.mk' (E →L[Real] E →L[Real] Real)
        (E := fun x : M =>
          TangentSpace I x →L[Real] TangentSpace I x →L[Real] Real)
        p.proj (g.inner p.proj)) :=
    g.contMDiff.continuous.comp
      (FiberBundle.continuous_proj E (TangentSpace I))
  have hvec : Continuous (fun p : TangentBundle I M =>
      TotalSpace.mk' E (E := fun x : M => TangentSpace I x) p.proj p.2) :=
    continuous_id
  have htotal := Continuous.clm_bundle_apply₂
    (𝕜 := Real) (F₁ := E) (F₂ := E) (F₃ := Real)
    (E₁ := TangentSpace I) (E₂ := TangentSpace I)
    (E₃ := Bundle.Trivial M Real)
    (b := fun p : TangentBundle I M => p.proj)
    hmetric hvec hvec
  have hprod :
      Continuous (fun p : TangentBundle I M =>
        (Bundle.Trivial.homeomorphProd M Real)
          (TotalSpace.mk' Real (E := Bundle.Trivial M Real)
            p.proj (g.inner p.proj p.2 p.2))) :=
    (Bundle.Trivial.homeomorphProd M Real).continuous.comp htotal
  simpa [Bundle.Trivial.homeomorphProd, TotalSpace.toProd] using
    (continuous_snd.comp hprod)


omit [FiniteDimensional ℝ E] in
theorem metricUnit_closed
    (g : SmoothRiemannianMetric I M) :
    IsClosed {p : TangentBundle I M | g.inner p.proj p.2 p.2 = 1} := by
  simpa [Set.setOf_eq_eq_singleton] using
    isClosed_singleton.preimage (metricQuad_cont (I := I) (M := M) g)



private theorem coordMetric_lower
    [T2Space M]
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    {K : Set M}
    (hK : IsCompact K)
    (hKsub : K ⊆ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    ∃ c : Real, 0 < c ∧
      ∀ x ∈ K, ∀ w : E, ‖w‖ = 1 →
        c ≤ g.inner x
          ((trivializationAt E (TangentSpace I) x₀).symmL Real x w)
          ((trivializationAt E (TangentSpace I) x₀).symmL Real x w) := by
  classical
  let e := trivializationAt E (TangentSpace I) x₀
  let S : Set (M × E) := K ×ˢ Metric.sphere (0 : E) 1
  have hScompact : IsCompact S := hK.prod (isCompact_sphere (0 : E) 1)
  have hSsub : S ⊆ e.baseSet ×ˢ (Set.univ : Set E) := by
    intro z hz
    exact ⟨hKsub hz.1, Set.mem_univ z.2⟩
  have hsymm_cont : ContinuousOn
      (fun z : M × E =>
        TotalSpace.mk' E (E := fun x : M => TangentSpace I x)
          z.1 (e.symm z.1 z.2)) S :=
    e.continuousOn_symm.mono hSsub
  have hq_cont : ContinuousOn
      (fun z : M × E =>
        g.inner z.1 (e.symmL Real z.1 z.2) (e.symmL Real z.1 z.2)) S := by
    refine ContinuousOn.congr
      ((metricQuad_cont (I := I) (M := M) g).continuousOn.comp hsymm_cont
        (fun _ _ => Set.mem_univ _)) ?_
    intro z hz
    simp [e, Trivialization.symmL_apply]
  have hq_pos : ∀ z ∈ S,
      0 < g.inner z.1 (e.symmL Real z.1 z.2) (e.symmL Real z.1 z.2) := by
    intro z hz
    have hx : z.1 ∈ e.baseSet := hKsub hz.1
    have hnorm : ‖z.2‖ = 1 := by
      simpa [Metric.sphere, dist_eq_norm] using hz.2
    have hw_ne : z.2 ≠ 0 := by
      intro hzero
      simp [hzero] at hnorm
    have hv_ne : e.symmL Real z.1 z.2 ≠ 0 := by
      intro hv
      have hforward :
          e.continuousLinearMapAt Real z.1 (e.symmL Real z.1 z.2) = z.2 :=
        e.continuousLinearMapAt_symmL (R := Real) hx z.2
      rw [hv, map_zero] at hforward
      exact hw_ne (by simpa using hforward.symm)
    exact g.pos z.1 (e.symmL Real z.1 z.2) hv_ne
  by_cases hSne : S.Nonempty
  · obtain ⟨z₀, hz₀, hmin⟩ := hScompact.exists_isMinOn hSne hq_cont
    let c : Real :=
      g.inner z₀.1 (e.symmL Real z₀.1 z₀.2) (e.symmL Real z₀.1 z₀.2)
    refine ⟨c, hq_pos z₀ hz₀, ?_⟩
    intro x hxK w hw
    have hz : (x, w) ∈ S := by
      exact ⟨hxK, by simpa [Metric.sphere, dist_eq_norm] using hw⟩
    exact (isMinOn_iff.mp hmin) (x, w) hz
  · refine ⟨1, zero_lt_one, ?_⟩
    intro x hxK w hw
    exfalso
    exact hSne ⟨(x, w), ⟨hxK, by simpa [Metric.sphere, dist_eq_norm] using hw⟩⟩



private theorem coordMetric_bound
    [T2Space M]
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    {K : Set M}
    (hK : IsCompact K)
    (hKsub : K ⊆ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    ∃ R : Real, 0 ≤ R ∧
      ∀ y ∈ K, ∀ v : TangentSpace I y,
        g.inner y v v = 1 →
          ‖(trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt Real y v‖ ≤ R := by
  classical
  let e := trivializationAt E (TangentSpace I) x₀
  obtain ⟨c, hcpos, hclower⟩ :=
    coordMetric_lower (I := I) (M := M) g x₀ hK hKsub
  refine ⟨c⁻¹ + 1, by positivity, ?_⟩
  intro y hyK v hunit
  have hybase : y ∈ e.baseSet := hKsub hyK
  let w : E := e.continuousLinearMapAt Real y v
  let r : Real := ‖w‖
  have hr_nonneg : 0 ≤ r := norm_nonneg w
  by_cases hw : w = 0
  · change r ≤ c⁻¹ + 1
    have hr0 : r = 0 := by simp [r, hw]
    rw [hr0]
    positivity
  have hrpos : 0 < r := by
    simpa [r] using (norm_pos_iff.mpr hw)
  let u : E := r⁻¹ • w
  have hnormu : ‖u‖ = 1 := by
    calc
      ‖u‖ = |r⁻¹| * ‖w‖ := by simp [u, norm_smul]
      _ = r⁻¹ * r := by
        rw [abs_of_pos (inv_pos.mpr hrpos)]
      _ = 1 := by
        exact inv_mul_cancel₀ (ne_of_gt hrpos)
  have hv_from_w : e.symmL Real y w = v := by
    simpa [w] using e.symmL_continuousLinearMapAt (R := Real) hybase v
  have hsymm_u : e.symmL Real y u = r⁻¹ • v := by
    change e.symmL Real y (r⁻¹ • w) = r⁻¹ • v
    rw [map_smul, hv_from_w]
  have hq_u :
      g.inner y (e.symmL Real y u) (e.symmL Real y u) = r⁻¹ * r⁻¹ := by
    calc
      g.inner y (e.symmL Real y u) (e.symmL Real y u)
          = g.inner y (r⁻¹ • v) (r⁻¹ • v) := by rw [hsymm_u]
      _ = r⁻¹ * (r⁻¹ * g.inner y v v) := by
        simp [smul_eq_mul]
      _ = r⁻¹ * r⁻¹ := by rw [hunit]; ring
  have hc_le : c ≤ r⁻¹ * r⁻¹ := by
    have hc_le' := hclower y hyK u hnormu
    rw [hq_u] at hc_le'
    exact hc_le'
  have hmul : c * (r * r) ≤ 1 := by
    have hrr_nonneg : 0 ≤ r * r := mul_nonneg hr_nonneg hr_nonneg
    have hle := mul_le_mul_of_nonneg_right hc_le hrr_nonneg
    have hright : (r⁻¹ * r⁻¹) * (r * r) = 1 := by
      field_simp [ne_of_gt hrpos]
    simpa [hright, mul_assoc, mul_comm, mul_left_comm] using hle
  have hsqr_le : r * r ≤ c⁻¹ := by
    have := (le_inv_mul_iff₀ hcpos).2 hmul
    simpa using this
  by_cases hrle : r ≤ 1
  · have hc_inv_nonneg : 0 ≤ c⁻¹ := by positivity
    linarith
  · have hone_le : 1 ≤ r := le_of_lt (lt_of_not_ge hrle)
    have hr_le_sq : r ≤ r * r := by nlinarith
    linarith



private theorem unitRest_compact
    [T2Space M]
    (g : SmoothRiemannianMetric I M)
    (e : Bundle.Trivialization E
      (Bundle.TotalSpace.proj : Bundle.TotalSpace E
        (TangentSpace I : M → Type _) → M))
    [e.IsLinear Real]
    {K : Set M} (hK : IsCompact K) (hKe : K ⊆ e.baseSet)
    {R : Real} (_hR : 0 ≤ R)
    (hbound : ∀ y ∈ K, ∀ v : TangentSpace I y,
      g.inner y v v = 1 →
        ‖e.continuousLinearMapAt Real y v‖ ≤ R) :
    IsCompact {p : MetricUnitTangent (I := I) (M := M) g |
      MetricUnitTangent.base (I := I) (M := M) p ∈ K} := by
  classical
  let Kball : Set (K × E) :=
    {z | z.2 ∈ Metric.closedBall (0 : E) R}
  have hKball : IsCompact Kball := by
    have hKc : CompactSpace K := isCompact_iff_compactSpace.mp hK
    letI : CompactSpace K := hKc
    have hball : IsCompact (Metric.closedBall (0 : E) R) :=
      isCompact_closedBall (0 : E) R
    convert
      (isCompact_univ.prod hball :
        IsCompact ((Set.univ : Set K) ×ˢ Metric.closedBall (0 : E) R))
      using 1
    ext z
    simp [Kball]
  let toTan : K × E → TangentBundle I M :=
    fun z =>
      TotalSpace.mk' E (E := fun x : M => TangentSpace I x)
        z.1.1 (e.symmL Real z.1.1 z.2)
  have htoTan : ContinuousOn toTan Kball := by
    have hpair : Continuous (fun z : K × E => (z.1.1, z.2)) :=
      (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
    have hmaps : MapsTo (fun z : K × E => (z.1.1, z.2)) Kball
        (e.baseSet ×ˢ (Set.univ : Set E)) := by
      intro z hz
      exact ⟨hKe z.1.2, Set.mem_univ _⟩
    have hsymm := e.continuousOn_symm.comp hpair.continuousOn hmaps
    refine hsymm.congr ?_
    intro z hz
    simp [toTan, Bundle.Trivialization.symmL_apply]
  let unitSet : Set (TangentBundle I M) :=
    {p | g.inner p.proj p.2 p.2 = 1}
  let D : Set (K × E) := Kball ∩ toTan ⁻¹' unitSet
  have hDcompact : IsCompact D := by
    have hclosed_pre : IsClosed (Kball ∩ toTan ⁻¹' unitSet) := by
      have hclosedUnit : IsClosed unitSet := by
        simpa [unitSet] using metricUnit_closed (I := I) (M := M) g
      exact htoTan.preimage_isClosed_of_isClosed hKball.isClosed hclosedUnit
    have hclosedD : IsClosed D := by
      simpa [D] using hclosed_pre
    exact hKball.of_isClosed_subset hclosedD inter_subset_left
  let mkUnit : D → MetricUnitTangent (I := I) (M := M) g :=
    fun z =>
      ⟨toTan z.1, by
        have hz : toTan z.1 ∈ unitSet := z.2.2
        simpa [unitSet] using hz⟩
  have hmkCont : Continuous mkUnit := by
    have hsub : Continuous (fun z : D => toTan z.1) := by
      rw [← continuousOn_univ]
      exact htoTan.comp continuous_subtype_val.continuousOn
        (fun z _ => z.2.1)
    exact Continuous.subtype_mk hsub (fun z => by
      have hz : toTan z.1 ∈ unitSet := z.2.2
      simpa [unitSet] using hz)
  have hlocal :
      {p : MetricUnitTangent (I := I) (M := M) g |
        MetricUnitTangent.base (I := I) (M := M) p ∈ K} =
        Set.range mkUnit := by
    ext p
    constructor
    · intro hpK
      let y : K := ⟨MetricUnitTangent.base (I := I) (M := M) p, hpK⟩
      let w : E :=
        e.continuousLinearMapAt Real y.1
          (MetricUnitTangent.vec (I := I) (M := M) p)
      have hwball : w ∈ Metric.closedBall (0 : E) R := by
        have hle := hbound y.1 y.2
          (MetricUnitTangent.vec (I := I) (M := M) p)
          (MetricUnitTangent.unit (I := I) (M := M) p)
        simpa [w, Metric.mem_closedBall, dist_eq_norm] using hle
      let z0 : K × E := (y, w)
      have hz0K : z0 ∈ Kball := by
        simpa [Kball, z0] using hwball
      have hz0unit : toTan z0 ∈ unitSet := by
        have hybase : y.1 ∈ e.baseSet := hKe y.2
        have hsymm :
            e.symmL Real y.1
              (e.continuousLinearMapAt Real y.1
                (MetricUnitTangent.vec (I := I) (M := M) p)) =
              MetricUnitTangent.vec (I := I) (M := M) p :=
          e.symmL_continuousLinearMapAt (R := Real) hybase
            (MetricUnitTangent.vec (I := I) (M := M) p)
        change
          g.inner y.1 (e.symmL Real y.1 w) (e.symmL Real y.1 w) = 1
        rw [show e.symmL Real y.1 w =
            MetricUnitTangent.vec (I := I) (M := M) p by
          simpa [w] using hsymm]
        exact MetricUnitTangent.unit (I := I) (M := M) p
      let z : D := ⟨z0, ⟨hz0K, hz0unit⟩⟩
      refine ⟨z, ?_⟩
      apply Subtype.ext
      change toTan z0 = p.1
      have hybase : y.1 ∈ e.baseSet := hKe y.2
      have hsymm :
          e.symmL Real y.1 w =
            MetricUnitTangent.vec (I := I) (M := M) p := by
        simpa [w] using
          e.symmL_continuousLinearMapAt (R := Real) hybase
            (MetricUnitTangent.vec (I := I) (M := M) p)
      cases p with
      | mk p hpunit =>
        cases p with
        | mk x v =>
          change
            (TotalSpace.mk' E (E := fun x : M => TangentSpace I x)
              x (e.symmL Real x w)) =
            (⟨x, v⟩ : TangentBundle I M)
          rw [show e.symmL Real x w = v by
            simpa [MetricUnitTangent.base, MetricUnitTangent.vec] using hsymm]
    · rintro ⟨z, rfl⟩
      exact z.1.1.2
  rw [hlocal]
  haveI : CompactSpace D := isCompact_iff_compactSpace.mp hDcompact
  exact isCompact_range hmkCont






theorem metricUnit_compact
    [CompactSpace M] [SigmaCompactSpace M] [T2Space M]
    (g : SmoothRiemannianMetric I M) :
    IsCompact (Set.univ : Set (MetricUnitTangent (I := I) (M := M) g)) := by
  classical
  let U : M → Set M := fun x => (trivializationAt E (TangentSpace I) x).baseSet
  have hUopen : ∀ x : M, IsOpen (U x) := by
    intro x
    exact (trivializationAt E (TangentSpace I) x).open_baseSet
  have hUcover : (Set.univ : Set M) ⊆ ⋃ x : M, U x := by
    intro y hy
    exact mem_iUnion.mpr
      ⟨y, mem_baseSet_trivializationAt E (TangentSpace I) y⟩
  obtain ⟨t, htcover⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set M)).elim_finite_subcover
      U hUopen hUcover
  obtain ⟨K, hKcompact, hKsub, hKeq⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set M)).finite_compact_cover
      t U (fun i _ => hUopen i) htcover
  let loc : M → Set (MetricUnitTangent (I := I) (M := M) g) :=
    fun i => {p | MetricUnitTangent.base (I := I) (M := M) p ∈ K i}
  have hlocal_compact : ∀ i ∈ t, IsCompact (loc i) := by
    intro i hi
    obtain ⟨R, hR, hbound⟩ :=
      coordMetric_bound (I := I) (M := M) g i
        (hKcompact i) (by simpa [U] using hKsub i)
    simpa [loc] using
      unitRest_compact (I := I) (M := M) g
        (trivializationAt E (TangentSpace I) i)
        (hKcompact i) (by simpa [U] using hKsub i) hR hbound
  have hunion :
      (Set.univ : Set (MetricUnitTangent (I := I) (M := M) g)) =
        ⋃ i ∈ t, loc i := by
    ext p
    constructor
    · intro hp
      have hbase : MetricUnitTangent.base (I := I) (M := M) p ∈
          (Set.univ : Set M) := Set.mem_univ _
      rw [hKeq] at hbase
      simpa [loc] using hbase
    · intro hp
      exact Set.mem_univ p
  rw [hunion]
  exact t.isCompact_biUnion hlocal_compact






theorem metricUnit_quadCont
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := ∞) 2) :
    Continuous (fun p : MetricUnitTangent (I := I) (M := M) g =>
      quad02 (I := I) (M := M)
        (A (MetricUnitTangent.base (I := I) (M := M) p))
        (MetricUnitTangent.vec (I := I) (M := M) p)) := by
  let b : MetricUnitTangent (I := I) (M := M) g → M :=
    fun p => MetricUnitTangent.base (I := I) (M := M) p
  let v : Fin 2 →
      (p : MetricUnitTangent (I := I) (M := M) g) → TangentSpace I (b p) :=
    fun _ p => MetricUnitTangent.vec (I := I) (M := M) p
  have hb : Continuous b := by
    dsimp [b, MetricUnitTangent.base]
    exact (FiberBundle.continuous_proj E (TangentSpace I)).comp continuous_subtype_val
  have hv : ∀ i : Fin 2, Continuous (fun p : MetricUnitTangent (I := I) (M := M) g =>
      TotalSpace.mk' E (E := fun x : M => TangentSpace I x) (b p) (v i p)) := by
    intro i
    simpa [b, v, MetricUnitTangent.base, MetricUnitTangent.vec] using
      (continuous_subtype_val :
        Continuous (fun p : MetricUnitTangent (I := I) (M := M) g =>
          (p.1 : TangentBundle I M)))
  have hAsec : Continuous (fun x : M =>
      TotalSpace.mk' (Tensor0SModel 2 Real E)
        (E := fun y : M => Tensor0SSpace 2 I y) x (A x)) :=
    A.contMDiff.continuous
  have hA : Continuous (fun p : MetricUnitTangent (I := I) (M := M) g =>
      TotalSpace.mk' (Tensor0SModel 2 Real E)
        (E := fun y : M => Tensor0SSpace 2 I y) (b p) (A (b p))) :=
    hAsec.comp hb
  have hEval := TensorMultilinear.continuous_section_apply_base
    (𝕜 := Real) (I := I) (M := M) (P := MetricUnitTangent (I := I) (M := M) g)
    (n := 2) b hb (fun p => A (b p)) hA v hv
  simpa [quad02, b, v] using hEval


omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem tensor02_smul2
    {x : M}
    (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (a : Real) (v : TangentSpace I x) :
    quad02 (I := I) (M := M) A (a • v) =
      a * a * quad02 (I := I) (M := M) A v := by
  have hmap := A.map_smul_univ (fun _ : Fin 2 => a) (fun _ : Fin 2 => v)
  have hslots :
      (fun i : Fin 2 => (fun _ : Fin 2 => a) i • (fun _ : Fin 2 => v) i) =
        (fun _ : Fin 2 => a • v) := by
    funext i
    simp
  rw [hslots] at hmap
  simpa [quad02, Fin.prod_univ_two, pow_two, smul_eq_mul,
    mul_assoc, mul_comm, mul_left_comm] using hmap


omit [FiniteDimensional ℝ E] [IsManifold I 1 M] in
theorem metric_smul2
    (g : SmoothRiemannianMetric I M) {x : M}
    (a : Real) (v : TangentSpace I x) :
    g.inner x (a • v) (a • v) = a * a * g.inner x v v := by
  calc
    g.inner x (a • v) (a • v) = a * g.inner x v (a • v) := by
      simp [smul_eq_mul]
    _ = a * (a * g.inner x v v) := by
      congr 1
      simp [smul_eq_mul]
    _ = a * a * g.inner x v v := by ring


end DifferentialGeometry
