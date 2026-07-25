import DifferentialGeometry.Geometry.Geodesic.Equation
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.ChartGramChristoffel
import Mathlib.Analysis.ODE.Gronwall



noncomputable section

open Set Function Filter Manifold Bundle
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace AlongCurve

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Riemannian.Geodesic

@[ext] structure SectionAlongCurve (I : ModelWithCorners ℝ E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (_γ : ℝ → M) where

  toFun : ℝ → E

namespace SectionAlongCurve

variable {γ : ℝ → M}

def zero : SectionAlongCurve I M γ := ⟨fun _ => 0⟩

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
@[simp] lemma zero_toFun (t : ℝ) : (zero : SectionAlongCurve I M γ).toFun t = 0 := rfl

def add (X Y : SectionAlongCurve I M γ) : SectionAlongCurve I M γ :=
  ⟨fun t => X.toFun t + Y.toFun t⟩

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
@[simp] lemma add_toFun (X Y : SectionAlongCurve I M γ) (t : ℝ) :
    (add X Y).toFun t = X.toFun t + Y.toFun t := rfl

def neg (X : SectionAlongCurve I M γ) : SectionAlongCurve I M γ :=
  ⟨fun t => - X.toFun t⟩

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
@[simp] lemma neg_toFun (X : SectionAlongCurve I M γ) (t : ℝ) :
    (neg X).toFun t = - X.toFun t := rfl

def sub (X Y : SectionAlongCurve I M γ) : SectionAlongCurve I M γ :=
  ⟨fun t => X.toFun t - Y.toFun t⟩

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
@[simp] lemma sub_toFun (X Y : SectionAlongCurve I M γ) (t : ℝ) :
    (sub X Y).toFun t = X.toFun t - Y.toFun t := rfl

def smul (a : ℝ) (X : SectionAlongCurve I M γ) : SectionAlongCurve I M γ :=
  ⟨fun t => a • X.toFun t⟩

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
@[simp] lemma smul_toFun (a : ℝ) (X : SectionAlongCurve I M γ) (t : ℝ) :
    (smul a X).toFun t = a • X.toFun t := rfl

omit [Module.Finite ℝ E] in
def smulFun (f : ℝ → ℝ) (X : SectionAlongCurve I M γ) : SectionAlongCurve I M γ :=
  ⟨fun t => f t • X.toFun t⟩

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
@[simp] lemma smulFun_toFun (f : ℝ → ℝ) (X : SectionAlongCurve I M γ) (t : ℝ) :
    (smulFun f X).toFun t = f t • X.toFun t := rfl

instance : CoeFun (SectionAlongCurve I M γ) (fun _ => ℝ → E) := ⟨toFun⟩

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
@[simp] lemma coe_zero : ((zero : SectionAlongCurve I M γ) : ℝ → E) = fun _ => 0 := rfl

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
@[simp] lemma coe_add (X Y : SectionAlongCurve I M γ) :
    ((add X Y : SectionAlongCurve I M γ) : ℝ → E) = fun t => X.toFun t + Y.toFun t := rfl

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
@[simp] lemma coe_smul (a : ℝ) (X : SectionAlongCurve I M γ) :
    ((smul a X : SectionAlongCurve I M γ) : ℝ → E) = fun t => a • X.toFun t := rfl

def ContMDiffOnInChart (n : WithTop ℕ∞) (X : SectionAlongCurve I M γ) (s : Set ℝ) : Prop :=
  ContDiffOn ℝ n X.toFun s

def ContMDiffAtInChart (n : WithTop ℕ∞) (X : SectionAlongCurve I M γ) (t : ℝ) : Prop :=
  ContDiffAt ℝ n X.toFun t

def DifferentiableOnAlong (X : SectionAlongCurve I M γ) (s : Set ℝ) : Prop :=
  DifferentiableOn ℝ X.toFun s

def DifferentiableAtAlong (X : SectionAlongCurve I M γ) (t : ℝ) : Prop :=
  DifferentiableAt ℝ X.toFun t

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
@[simp] lemma contMDiffOnInChart_def (n : WithTop ℕ∞) (X : SectionAlongCurve I M γ) (s : Set ℝ) :
    ContMDiffOnInChart (I := I) (M := M) n X s = ContDiffOn ℝ n X.toFun s := rfl

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
@[simp] lemma contMDiffAtInChart_def (n : WithTop ℕ∞) (X : SectionAlongCurve I M γ) (t : ℝ) :
    ContMDiffAtInChart (I := I) (M := M) n X t = ContDiffAt ℝ n X.toFun t := rfl

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma zero_contMDiffOnInChart (n : WithTop ℕ∞) (s : Set ℝ) :
    ContMDiffOnInChart (I := I) (M := M) (γ := γ) n zero s := by
  unfold ContMDiffOnInChart
  exact contDiffOn_const

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma zero_contMDiffAtInChart (n : WithTop ℕ∞) (t : ℝ) :
    ContMDiffAtInChart (I := I) (M := M) (γ := γ) n zero t := by
  unfold ContMDiffAtInChart
  exact contDiffAt_const

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma add_contMDiffOnInChart {n : WithTop ℕ∞} {X Y : SectionAlongCurve I M γ} {s : Set ℝ}
    (hX : ContMDiffOnInChart (I := I) (M := M) n X s)
    (hY : ContMDiffOnInChart (I := I) (M := M) n Y s) :
    ContMDiffOnInChart (I := I) (M := M) n (add X Y) s := by
  unfold ContMDiffOnInChart at *
  exact hX.add hY

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma add_contMDiffAtInChart {n : WithTop ℕ∞} {X Y : SectionAlongCurve I M γ} {t : ℝ}
    (hX : ContMDiffAtInChart (I := I) (M := M) n X t)
    (hY : ContMDiffAtInChart (I := I) (M := M) n Y t) :
    ContMDiffAtInChart (I := I) (M := M) n (add X Y) t := by
  unfold ContMDiffAtInChart at *
  exact hX.add hY

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma neg_contMDiffOnInChart {n : WithTop ℕ∞} {X : SectionAlongCurve I M γ} {s : Set ℝ}
    (hX : ContMDiffOnInChart (I := I) (M := M) n X s) :
    ContMDiffOnInChart (I := I) (M := M) n (neg X) s := by
  unfold ContMDiffOnInChart at *
  exact hX.neg

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma sub_contMDiffOnInChart {n : WithTop ℕ∞} {X Y : SectionAlongCurve I M γ} {s : Set ℝ}
    (hX : ContMDiffOnInChart (I := I) (M := M) n X s)
    (hY : ContMDiffOnInChart (I := I) (M := M) n Y s) :
    ContMDiffOnInChart (I := I) (M := M) n (sub X Y) s := by
  unfold ContMDiffOnInChart at *
  exact hX.sub hY

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma smul_contMDiffOnInChart {n : WithTop ℕ∞} {a : ℝ} {X : SectionAlongCurve I M γ} {s : Set ℝ}
    (hX : ContMDiffOnInChart (I := I) (M := M) n X s) :
    ContMDiffOnInChart (I := I) (M := M) n (smul a X) s := by
  unfold ContMDiffOnInChart at *
  exact hX.const_smul a

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma smulFun_contMDiffOnInChart {n : WithTop ℕ∞} {f : ℝ → ℝ}
    {X : SectionAlongCurve I M γ} {s : Set ℝ}
    (hf : ContDiffOn ℝ n f s)
    (hX : ContMDiffOnInChart (I := I) (M := M) n X s) :
    ContMDiffOnInChart (I := I) (M := M) n (smulFun f X) s := by
  unfold ContMDiffOnInChart at *
  exact hf.smul hX

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma add_differentiableOnAlong {X Y : SectionAlongCurve I M γ} {s : Set ℝ}
    (hX : DifferentiableOnAlong (I := I) (M := M) X s)
    (hY : DifferentiableOnAlong (I := I) (M := M) Y s) :
    DifferentiableOnAlong (I := I) (M := M) (add X Y) s := by
  unfold DifferentiableOnAlong at *
  exact hX.add hY

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma smul_differentiableOnAlong {a : ℝ} {X : SectionAlongCurve I M γ} {s : Set ℝ}
    (hX : DifferentiableOnAlong (I := I) (M := M) X s) :
    DifferentiableOnAlong (I := I) (M := M) (smul a X) s := by
  unfold DifferentiableOnAlong at *
  exact hX.const_smul a

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma smulFun_differentiableOnAlong {f : ℝ → ℝ} {X : SectionAlongCurve I M γ} {s : Set ℝ}
    (hf : DifferentiableOn ℝ f s)
    (hX : DifferentiableOnAlong (I := I) (M := M) X s) :
    DifferentiableOnAlong (I := I) (M := M) (smulFun f X) s := by
  unfold DifferentiableOnAlong at *
  exact hf.smul hX

end SectionAlongCurve

def chartCurve (α : M) (γ : ℝ → M) : ℝ → E :=
  fun t => extChartAt I α (γ t)

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] in
@[simp] lemma chartCurve_def (α : M) (γ : ℝ → M) (t : ℝ) :
    chartCurve (I := I) α γ t = extChartAt I α (γ t) := rfl

def chartCovDerivAlong (g : SmoothRiemannianMetric I M) (α : M) (γ : ℝ → M)
    (X : ℝ → E) (t : ℝ) : E :=
  deriv X t +
    chartChristoffelContraction (I := I) g α
      (deriv (chartCurve (I := I) α γ) t) (X t)
      (chartCurve (I := I) α γ t)

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma chartCovDerivAlong_def
    (g : SmoothRiemannianMetric I M) (α : M) (γ : ℝ → M)
    (X : ℝ → E) (t : ℝ) :
    chartCovDerivAlong (I := I) g α γ X t =
      deriv X t +
        chartChristoffelContraction (I := I) g α
          (deriv (chartCurve (I := I) α γ) t) (X t)
          (chartCurve (I := I) α γ t) := rfl

namespace ChartChristoffel

variable {g : SmoothRiemannianMetric I M} {α : M} {y : E}

omit [NeZero (Module.finrank ℝ E)] in
lemma contraction_add_right (v w₁ w₂ : E) :
    chartChristoffelContraction (I := I) g α v (w₁ + w₂) y =
      chartChristoffelContraction (I := I) g α v w₁ y +
        chartChristoffelContraction (I := I) g α v w₂ y := by
  classical
  unfold chartChristoffelContraction
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [← add_smul]
  congr 1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [show chartCoord (E := E) j (w₁ + w₂) =
      chartCoord (E := E) j w₁ + chartCoord (E := E) j w₂ from by
    unfold chartCoord; simp]
  ring

omit [NeZero (Module.finrank ℝ E)] in
lemma contraction_add_left (v₁ v₂ w : E) :
    chartChristoffelContraction (I := I) g α (v₁ + v₂) w y =
      chartChristoffelContraction (I := I) g α v₁ w y +
        chartChristoffelContraction (I := I) g α v₂ w y := by
  rw [chartChristoffelContraction_symm, contraction_add_right,
    chartChristoffelContraction_symm (v := v₁) (w := w),
    chartChristoffelContraction_symm (v := v₂) (w := w)]

omit [NeZero (Module.finrank ℝ E)] in
lemma contraction_smul_right (a : ℝ) (v w : E) :
    chartChristoffelContraction (I := I) g α v (a • w) y =
      a • chartChristoffelContraction (I := I) g α v w y := by
  classical
  unfold chartChristoffelContraction
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [smul_smul]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [chartCoord_smul]
  ring

omit [NeZero (Module.finrank ℝ E)] in
lemma contraction_smul_left (a : ℝ) (v w : E) :
    chartChristoffelContraction (I := I) g α (a • v) w y =
      a • chartChristoffelContraction (I := I) g α v w y := by
  rw [chartChristoffelContraction_symm, contraction_smul_right,
    chartChristoffelContraction_symm (v := v) (w := w)]

omit [NeZero (Module.finrank ℝ E)] in
lemma contraction_zero_right (v : E) :
    chartChristoffelContraction (I := I) g α v (0 : E) y = 0 := by
  rw [chartChristoffelContraction_symm, chartChristoffelContraction_zero_left]

end ChartChristoffel

def chartChristoffelContractionRightCLM
    (g : SmoothRiemannianMetric I M) (α : M) (v : E) (y : E) : E →L[ℝ] E :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w => chartChristoffelContraction (I := I) g α v w y
      map_add' := fun w₁ w₂ => ChartChristoffel.contraction_add_right v w₁ w₂
      map_smul' := fun a w => ChartChristoffel.contraction_smul_right a v w }

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma chartChristoffelContractionRightCLM_apply
    (g : SmoothRiemannianMetric I M) (α : M) (v : E) (y : E) (w : E) :
    chartChristoffelContractionRightCLM (I := I) g α v y w =
      chartChristoffelContraction (I := I) g α v w y := rfl

omit [NeZero (Module.finrank ℝ E)] in
lemma chartCovDerivAlong_eq_add_clm
    (g : SmoothRiemannianMetric I M) (α : M) (γ : ℝ → M)
    (X : ℝ → E) (t : ℝ) :
    chartCovDerivAlong (I := I) g α γ X t =
      deriv X t +
        chartChristoffelContractionRightCLM (I := I) g α
          (deriv (chartCurve (I := I) α γ) t)
          (chartCurve (I := I) α γ t) (X t) := rfl

def IsCovDerivAlongChart (g : SmoothRiemannianMetric I M) (α : M) (γ : ℝ → M)
    (uPrime : ℝ → E) (Y W : ℝ → E) (s : Set ℝ) : Prop :=
  (∀ t ∈ s, HasDerivAt (chartCurve (I := I) α γ) (uPrime t) t) ∧
    ∀ t ∈ s, HasDerivAt Y
      (W t - chartChristoffelContraction (I := I) g α (uPrime t) (Y t)
          (chartCurve (I := I) α γ t)) t

omit [NeZero (Module.finrank ℝ E)] in
lemma IsCovDerivAlongChart.hasDerivAt_eq
    {g : SmoothRiemannianMetric I M} {α : M} {γ : ℝ → M} {uPrime Y W : ℝ → E} {s : Set ℝ}
    (h : IsCovDerivAlongChart (I := I) g α γ uPrime Y W s) {t : ℝ} (ht : t ∈ s) :
    HasDerivAt Y
      (W t - chartChristoffelContraction (I := I) g α (uPrime t) (Y t)
          (chartCurve (I := I) α γ t)) t :=
  h.2 t ht

omit [NeZero (Module.finrank ℝ E)] in
theorem IsCovDerivAlongChart.add
    {g : SmoothRiemannianMetric I M} {α : M} {γ : ℝ → M} {uPrime : ℝ → E}
    {Y₁ Y₂ W₁ W₂ : ℝ → E} {s : Set ℝ}
    (h₁ : IsCovDerivAlongChart (I := I) g α γ uPrime Y₁ W₁ s)
    (h₂ : IsCovDerivAlongChart (I := I) g α γ uPrime Y₂ W₂ s) :
    IsCovDerivAlongChart (I := I) g α γ uPrime
      (fun t => Y₁ t + Y₂ t) (fun t => W₁ t + W₂ t) s := by
  refine ⟨h₁.1, ?_⟩
  intro t ht
  have hY₁ := h₁.2 t ht
  have hY₂ := h₂.2 t ht
  have hadd := hY₁.add hY₂
  have hΓadd :
      chartChristoffelContraction (I := I) g α (uPrime t) (Y₁ t + Y₂ t)
          (chartCurve (I := I) α γ t)
        = chartChristoffelContraction (I := I) g α (uPrime t) (Y₁ t)
              (chartCurve (I := I) α γ t)
          + chartChristoffelContraction (I := I) g α (uPrime t) (Y₂ t)
              (chartCurve (I := I) α γ t) :=
    ChartChristoffel.contraction_add_right (uPrime t) (Y₁ t) (Y₂ t)
  convert hadd using 1
  rw [hΓadd]; module

omit [NeZero (Module.finrank ℝ E)] in
theorem IsCovDerivAlongChart.smul
    {g : SmoothRiemannianMetric I M} {α : M} {γ : ℝ → M} {uPrime : ℝ → E}
    {Y W : ℝ → E} {s : Set ℝ}
    (h : IsCovDerivAlongChart (I := I) g α γ uPrime Y W s) (c : ℝ) :
    IsCovDerivAlongChart (I := I) g α γ uPrime
      (fun t => c • Y t) (fun t => c • W t) s := by
  refine ⟨h.1, ?_⟩
  intro t ht
  have hY := h.2 t ht
  have hcY := hY.const_smul c
  have hΓsmul :
      chartChristoffelContraction (I := I) g α (uPrime t) (c • Y t)
          (chartCurve (I := I) α γ t)
        = c • chartChristoffelContraction (I := I) g α (uPrime t) (Y t)
              (chartCurve (I := I) α γ t) :=
    ChartChristoffel.contraction_smul_right c (uPrime t) (Y t)
  convert hcY using 1
  rw [hΓsmul, smul_sub]

omit [NeZero (Module.finrank ℝ E)] in
theorem IsCovDerivAlongChart.neg
    {g : SmoothRiemannianMetric I M} {α : M} {γ : ℝ → M} {uPrime : ℝ → E}
    {Y W : ℝ → E} {s : Set ℝ}
    (h : IsCovDerivAlongChart (I := I) g α γ uPrime Y W s) :
    IsCovDerivAlongChart (I := I) g α γ uPrime
      (fun t => - Y t) (fun t => - W t) s := by
  have hsmul := IsCovDerivAlongChart.smul (h := h) (-1 : ℝ)
  have hYeq : (fun t : ℝ => (-1 : ℝ) • Y t) = (fun t : ℝ => - Y t) := by
    funext t; rw [neg_one_smul]
  have hWeq : (fun t : ℝ => (-1 : ℝ) • W t) = (fun t : ℝ => - W t) := by
    funext t; rw [neg_one_smul]
  rw [hYeq, hWeq] at hsmul
  exact hsmul

omit [NeZero (Module.finrank ℝ E)] in
theorem IsCovDerivAlongChart.zero
    (g : SmoothRiemannianMetric I M) (α : M) (γ : ℝ → M) (uPrime : ℝ → E) (s : Set ℝ)
    (hu : ∀ t ∈ s, HasDerivAt (chartCurve (I := I) α γ) (uPrime t) t) :
    IsCovDerivAlongChart (I := I) g α γ uPrime (fun _ => (0 : E)) (fun _ => (0 : E)) s := by
  refine ⟨hu, ?_⟩
  intro t _
  have hΓ0 : chartChristoffelContraction (I := I) g α (uPrime t) (0 : E)
        (chartCurve (I := I) α γ t) = 0 :=
    ChartChristoffel.contraction_zero_right (uPrime t)
  rw [hΓ0]; simpa using (hasDerivAt_const t (0 : E))

omit [NeZero (Module.finrank ℝ E)] in
theorem IsCovDerivAlongChart.smulFun
    {g : SmoothRiemannianMetric I M} {α : M} {γ : ℝ → M} {uPrime : ℝ → E}
    {Y W : ℝ → E} {s : Set ℝ}
    (h : IsCovDerivAlongChart (I := I) g α γ uPrime Y W s)
    {f : ℝ → ℝ} {fPrime : ℝ → ℝ}
    (hf : ∀ t ∈ s, HasDerivAt f (fPrime t) t) :
    IsCovDerivAlongChart (I := I) g α γ uPrime
      (fun t => f t • Y t)
      (fun t => fPrime t • Y t + f t • W t) s := by
  refine ⟨h.1, ?_⟩
  intro t ht
  have hY := h.2 t ht
  have hft := hf t ht
  have hfY := hft.smul hY
  have hΓsmul :
      chartChristoffelContraction (I := I) g α (uPrime t) (f t • Y t)
          (chartCurve (I := I) α γ t)
        = f t • chartChristoffelContraction (I := I) g α (uPrime t) (Y t)
              (chartCurve (I := I) α γ t) :=
    ChartChristoffel.contraction_smul_right (f t) (uPrime t) (Y t)
  convert hfY using 1
  rw [hΓsmul, smul_sub]; module

def IsParallelChart (g : SmoothRiemannianMetric I M) (α : M) (γ : ℝ → M)
    (uPrime : ℝ → E) (Y : ℝ → E) (s : Set ℝ) : Prop :=
  IsCovDerivAlongChart (I := I) g α γ uPrime Y (fun _ => (0 : E)) s

omit [NeZero (Module.finrank ℝ E)] in
lemma IsParallelChart.hasDerivAt
    {g : SmoothRiemannianMetric I M} {α : M} {γ : ℝ → M} {uPrime Y : ℝ → E} {s : Set ℝ}
    (h : IsParallelChart (I := I) g α γ uPrime Y s) {t : ℝ} (ht : t ∈ s) :
    HasDerivAt Y
      (- chartChristoffelContraction (I := I) g α (uPrime t) (Y t)
          (chartCurve (I := I) α γ t)) t := by
  have := h.2 t ht
  simpa using this

omit [NeZero (Module.finrank ℝ E)] in
lemma IsParallelChart.chartCurve_hasDerivAt
    {g : SmoothRiemannianMetric I M} {α : M} {γ : ℝ → M} {uPrime Y : ℝ → E} {s : Set ℝ}
    (h : IsParallelChart (I := I) g α γ uPrime Y s) {t : ℝ} (ht : t ∈ s) :
    HasDerivAt (chartCurve (I := I) α γ) (uPrime t) t :=
  h.1 t ht

omit [NeZero (Module.finrank ℝ E)] in
theorem IsParallelChart.smul
    {g : SmoothRiemannianMetric I M} {α : M} {γ : ℝ → M} {uPrime Y : ℝ → E} {s : Set ℝ}
    (h : IsParallelChart (I := I) g α γ uPrime Y s) (c : ℝ) :
    IsParallelChart (I := I) g α γ uPrime (fun t => c • Y t) s := by
  have hsmul := IsCovDerivAlongChart.smul (h := h) c
  have hzero : (fun t : ℝ => c • (0 : E)) = (fun _ : ℝ => (0 : E)) := by
    funext; simp
  rw [IsParallelChart]
  convert hsmul using 1
  exact hzero.symm

omit [NeZero (Module.finrank ℝ E)] in
theorem IsParallelChart.add
    {g : SmoothRiemannianMetric I M} {α : M} {γ : ℝ → M} {uPrime Y₁ Y₂ : ℝ → E} {s : Set ℝ}
    (h₁ : IsParallelChart (I := I) g α γ uPrime Y₁ s)
    (h₂ : IsParallelChart (I := I) g α γ uPrime Y₂ s) :
    IsParallelChart (I := I) g α γ uPrime (fun t => Y₁ t + Y₂ t) s := by
  have hadd := IsCovDerivAlongChart.add h₁ h₂
  have hzero : (fun t : ℝ => (0 : E) + 0) = (fun _ : ℝ => (0 : E)) := by
    funext; simp
  rw [IsParallelChart]
  convert hadd using 1
  exact hzero.symm

def ParallelTransportLipschitzBound (g : SmoothRiemannianMetric I M) (α : M) (γ : ℝ → M)
    (uPrime : ℝ → E) (K : NNReal) (s : Set ℝ) : Prop :=
  ∀ t ∈ s,
    ‖chartChristoffelContractionRightCLM (I := I) g α (uPrime t)
        (chartCurve (I := I) α γ t)‖₊ ≤ K

omit [NeZero (Module.finrank ℝ E)] in
theorem IsParallelChart.unique_of_initial
    {g : SmoothRiemannianMetric I M} {α : M} {γ : ℝ → M} {uPrime Y₁ Y₂ : ℝ → E}
    {a b t₀ : ℝ} {K : NNReal}
    (h₁ : IsParallelChart (I := I) g α γ uPrime Y₁ (Set.Ioo a b))
    (h₂ : IsParallelChart (I := I) g α γ uPrime Y₂ (Set.Ioo a b))
    (hK : ParallelTransportLipschitzBound (I := I) g α γ uPrime K (Set.Ioo a b))
    (ht₀ : t₀ ∈ Set.Ioo a b) (hinit : Y₁ t₀ = Y₂ t₀) :
    Set.EqOn Y₁ Y₂ (Set.Ioo a b) := by
  classical
  set v : ℝ → E → E :=
    fun t Y => - chartChristoffelContractionRightCLM (I := I) g α (uPrime t)
                  (chartCurve (I := I) α γ t) Y with hv_def
  have hLip : ∀ t ∈ Set.Ioo a b,
      LipschitzOnWith K (v t) (Set.univ : Set E) := by
    intro t ht
    have hclm : LipschitzWith ‖chartChristoffelContractionRightCLM (I := I) g α
        (uPrime t) (chartCurve (I := I) α γ t)‖₊
        (chartChristoffelContractionRightCLM (I := I) g α (uPrime t)
          (chartCurve (I := I) α γ t)) :=
      (chartChristoffelContractionRightCLM (I := I) g α (uPrime t)
          (chartCurve (I := I) α γ t)).lipschitz
    have hclm_neg : LipschitzWith ‖chartChristoffelContractionRightCLM (I := I) g α
        (uPrime t) (chartCurve (I := I) α γ t)‖₊
        (fun Y => - chartChristoffelContractionRightCLM (I := I) g α (uPrime t)
          (chartCurve (I := I) α γ t) Y) :=
      hclm.neg
    have hweak : LipschitzWith K
        (fun Y => - chartChristoffelContractionRightCLM (I := I) g α (uPrime t)
          (chartCurve (I := I) α γ t) Y) :=
      hclm_neg.weaken (hK t ht)
    exact hweak.lipschitzOnWith
  have hY₁ : ∀ t ∈ Set.Ioo a b, HasDerivAt Y₁ (v t (Y₁ t)) t ∧ Y₁ t ∈ (Set.univ : Set E) := by
    intro t ht
    refine ⟨?_, Set.mem_univ _⟩
    change HasDerivAt Y₁ (- chartChristoffelContractionRightCLM (I := I) g α (uPrime t)
      (chartCurve (I := I) α γ t) (Y₁ t)) t
    exact h₁.hasDerivAt ht
  have hY₂ : ∀ t ∈ Set.Ioo a b, HasDerivAt Y₂ (v t (Y₂ t)) t ∧ Y₂ t ∈ (Set.univ : Set E) := by
    intro t ht
    refine ⟨?_, Set.mem_univ _⟩
    change HasDerivAt Y₂ (- chartChristoffelContractionRightCLM (I := I) g α (uPrime t)
      (chartCurve (I := I) α γ t) (Y₂ t)) t
    exact h₂.hasDerivAt ht
  exact ODE_solution_unique_of_mem_Ioo hLip ht₀ hY₁ hY₂ hinit

omit [NeZero (Module.finrank ℝ E)] in
theorem IsParallelChart.unique_eventually
    {g : SmoothRiemannianMetric I M} {α : M} {γ : ℝ → M} {uPrime Y₁ Y₂ : ℝ → E}
    {t₀ : ℝ} {K : NNReal}
    (hLip : ∀ᶠ t in 𝓝 t₀, LipschitzOnWith K
      (fun Y : E => - chartChristoffelContractionRightCLM (I := I) g α (uPrime t)
        (chartCurve (I := I) α γ t) Y) (Set.univ : Set E))
    (h₁ : ∀ᶠ t in 𝓝 t₀, HasDerivAt Y₁
      (- chartChristoffelContraction (I := I) g α (uPrime t) (Y₁ t)
        (chartCurve (I := I) α γ t)) t)
    (h₂ : ∀ᶠ t in 𝓝 t₀, HasDerivAt Y₂
      (- chartChristoffelContraction (I := I) g α (uPrime t) (Y₂ t)
        (chartCurve (I := I) α γ t)) t)
    (hinit : Y₁ t₀ = Y₂ t₀) : Y₁ =ᶠ[𝓝 t₀] Y₂ := by
  classical
  have hYY₁ : ∀ᶠ t in 𝓝 t₀, HasDerivAt Y₁
      ((fun s : ℝ => - chartChristoffelContractionRightCLM (I := I) g α (uPrime s)
          (chartCurve (I := I) α γ s)) t (Y₁ t)) t ∧ Y₁ t ∈ (Set.univ : Set E) := by
    refine h₁.mono ?_
    intro t ht
    refine ⟨?_, Set.mem_univ _⟩
    simpa using ht
  have hYY₂ : ∀ᶠ t in 𝓝 t₀, HasDerivAt Y₂
      ((fun s : ℝ => - chartChristoffelContractionRightCLM (I := I) g α (uPrime s)
          (chartCurve (I := I) α γ s)) t (Y₂ t)) t ∧ Y₂ t ∈ (Set.univ : Set E) := by
    refine h₂.mono ?_
    intro t ht
    refine ⟨?_, Set.mem_univ _⟩
    simpa using ht
  exact ODE_solution_unique_of_eventually hLip hYY₁ hYY₂ hinit

def HasParallelTransportChart (g : SmoothRiemannianMetric I M) (α : M) (γ : ℝ → M)
    (uPrime : ℝ → E) (t₀ : ℝ) (v₀ : E) (Y : ℝ → E) (s : Set ℝ) : Prop :=
  IsParallelChart (I := I) g α γ uPrime Y s ∧ Y t₀ = v₀

omit [NeZero (Module.finrank ℝ E)] in
theorem HasParallelTransportChart.unique_of_lipschitz
    {g : SmoothRiemannianMetric I M} {α : M} {γ : ℝ → M} {uPrime Y₁ Y₂ : ℝ → E}
    {a b t₀ : ℝ} {v₀ : E} {K : NNReal}
    (h₁ : HasParallelTransportChart (I := I) g α γ uPrime t₀ v₀ Y₁ (Set.Ioo a b))
    (h₂ : HasParallelTransportChart (I := I) g α γ uPrime t₀ v₀ Y₂ (Set.Ioo a b))
    (hK : ParallelTransportLipschitzBound (I := I) g α γ uPrime K (Set.Ioo a b))
    (ht₀ : t₀ ∈ Set.Ioo a b) :
    Set.EqOn Y₁ Y₂ (Set.Ioo a b) :=
  IsParallelChart.unique_of_initial h₁.1 h₂.1 hK ht₀
    (h₁.2.trans h₂.2.symm)

omit [NeZero (Module.finrank ℝ E)] in
theorem HasParallelTransportChart.zero
    (g : SmoothRiemannianMetric I M) (α : M) (γ : ℝ → M) (uPrime : ℝ → E)
    (t₀ : ℝ) (s : Set ℝ)
    (hu : ∀ t ∈ s, HasDerivAt (chartCurve (I := I) α γ) (uPrime t) t) :
    HasParallelTransportChart (I := I) g α γ uPrime t₀ (0 : E) (fun _ => (0 : E)) s := by
  refine ⟨?_, rfl⟩
  exact IsCovDerivAlongChart.zero g α γ uPrime s hu

omit [NeZero (Module.finrank ℝ E)] in
theorem HasParallelTransportChart.linear_combination
    {g : SmoothRiemannianMetric I M} {α : M} {γ : ℝ → M} {uPrime Y₁ Y₂ : ℝ → E}
    {t₀ : ℝ} {v₁ v₂ : E} (a c : ℝ) {s : Set ℝ}
    (h₁ : HasParallelTransportChart (I := I) g α γ uPrime t₀ v₁ Y₁ s)
    (h₂ : HasParallelTransportChart (I := I) g α γ uPrime t₀ v₂ Y₂ s) :
    HasParallelTransportChart (I := I) g α γ uPrime t₀ (a • v₁ + c • v₂)
      (fun t => a • Y₁ t + c • Y₂ t) s := by
  refine ⟨?_, ?_⟩
  · have hY₁ := IsParallelChart.smul h₁.1 a
    have hY₂ := IsParallelChart.smul h₂.1 c
    exact IsParallelChart.add hY₁ hY₂
  · simp [h₁.2, h₂.2]

section MetricCompatibilityAlongCurve

open DifferentialGeometry.Integral.DivergenceTheorem

variable {g : SmoothRiemannianMetric I M} {α : M} {γ : ℝ → M}

def chartSectionCoord (X : ℝ → E) (i : Fin (Module.finrank ℝ E)) : ℝ → ℝ :=
  fun t => chartCoord (E := E) i (X t)

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma chartSectionCoord_def (X : ℝ → E) (i : Fin (Module.finrank ℝ E)) (t : ℝ) :
    chartSectionCoord (E := E) X i t = chartCoord (E := E) i (X t) := rfl

def chartGramAlongCurve (g : SmoothRiemannianMetric I M) (α : M) (γ : ℝ → M)
    (V W : ℝ → E) (t : ℝ) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
    chartGramOnE (I := I) g α i j (chartCurve (I := I) α γ t) *
      chartCoord (E := E) i (V t) * chartCoord (E := E) j (W t)

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma chartGramAlongCurve_def
    (g : SmoothRiemannianMetric I M) (α : M) (γ : ℝ → M) (V W : ℝ → E) (t : ℝ) :
    chartGramAlongCurve (I := I) g α γ V W t =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α i j (chartCurve (I := I) α γ t) *
          chartCoord (E := E) i (V t) * chartCoord (E := E) j (W t) := rfl

omit [NeZero (Module.finrank ℝ E)] in
lemma symmL_eq_sum_chartBasisVecFiber
    (α : M) {x : M}
    (v : E) :
    (trivializationAt E (TangentSpace I) α).symmL ℝ x v =
      ∑ i : Fin (Module.finrank ℝ E),
        chartCoord (E := E) i v • chartBasisVecFiber (I := I) α i x := by
  classical
  have hv : v = ∑ i : Fin (Module.finrank ℝ E),
      chartCoord (E := E) i v • (chartModelBasis E) i := by
    conv_lhs => rw [← (chartModelBasis E).sum_repr v]
    rfl
  conv_lhs => rw [hv]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [map_smul]
  rfl

omit [NeZero (Module.finrank ℝ E)] in
theorem inner_eq_chartGramOnE_bilinear_on_baseSet
    (g : SmoothRiemannianMetric I M) (α : M) {x : M}
    (V W : E) :
    g.inner x
        ((trivializationAt E (TangentSpace I) α).symmL ℝ x V)
        ((trivializationAt E (TangentSpace I) α).symmL ℝ x W) =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        chartGramMatrix (I := I) g α x i j *
          chartCoord (E := E) i V * chartCoord (E := E) j W := by
  classical
  rw [symmL_eq_sum_chartBasisVecFiber (I := I) α V,
      symmL_eq_sum_chartBasisVecFiber (I := I) α W]
  set vfib : Fin (Module.finrank ℝ E) → TangentSpace I x :=
    fun i => chartBasisVecFiber (I := I) α i x with hvfib
  have hL :
      g.inner x (∑ i, chartCoord (E := E) i V • vfib i)
        = ∑ i, chartCoord (E := E) i V • g.inner x (vfib i) := by
    rw [map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_smul]
  rw [hL, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [map_smul, smul_eq_mul, hvfib, chartGramMatrix_apply]
  ring

omit [NeZero (Module.finrank ℝ E)] in
lemma chartSectionCoord_hasDerivAt
    {X : ℝ → E} {Xprime : ℝ → E} {t : ℝ} (i : Fin (Module.finrank ℝ E))
    (hX : HasDerivAt X (Xprime t) t) :
    HasDerivAt (chartSectionCoord (E := E) X i)
      (chartCoord (E := E) i (Xprime t)) t := by
  set L : E →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap ((chartModelBasis E).coord i) with hL_def
  have hLapply : ∀ v : E, L v = chartCoord (E := E) i v := by
    intro v
    rw [hL_def]
    simp only [LinearMap.coe_toContinuousLinearMap']
    rfl
  have hcomp : HasDerivAt (fun s : ℝ => L (X s)) (L (Xprime t)) t :=
    L.hasFDerivAt.comp_hasDerivAt t hX
  have hfun : (fun s : ℝ => L (X s)) = chartSectionCoord (E := E) X i := by
    funext s; rw [hLapply, chartSectionCoord_def]
  rw [hfun, hLapply] at hcomp
  exact hcomp

omit [NeZero (Module.finrank ℝ E)] in
lemma fderiv_chartGramOnE_eq_sum_partialDeriv
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) (y v : E) :
    fderiv ℝ (chartGramOnE (I := I) g α i j) y v =
      ∑ k : Fin (Module.finrank ℝ E),
        chartCoord (E := E) k v *
          partialDeriv (E := E) k (chartGramOnE (I := I) g α i j) y := by
  classical
  have hv : v = ∑ k : Fin (Module.finrank ℝ E),
      chartCoord (E := E) k v • (chartModelBasis E) k := by
    conv_lhs => rw [← (chartModelBasis E).sum_repr v]
    rfl
  conv_lhs => rw [hv]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [map_smul, smul_eq_mul]
  rfl

omit [NeZero (Module.finrank ℝ E)] in
lemma chartGramOnE_comp_chartCurve_hasDerivAt
    (g : SmoothRiemannianMetric I M) (α : M) (γ : ℝ → M)
    (i j : Fin (Module.finrank ℝ E)) {uPrime : ℝ → E} {t : ℝ}
    (huPrime : HasDerivAt (chartCurve (I := I) α γ) (uPrime t) t)
    (hmem : chartCurve (I := I) α γ t ∈ interior (extChartAt I α).target) :
    HasDerivAt (fun s => chartGramOnE (I := I) g α i j (chartCurve (I := I) α γ s))
      (∑ k : Fin (Module.finrank ℝ E),
        chartCoord (E := E) k (uPrime t) *
          partialDeriv (E := E) k (chartGramOnE (I := I) g α i j)
            (chartCurve (I := I) α γ t)) t := by
  classical
  have hG_cd : ContDiffOn ℝ ∞ (chartGramOnE (I := I) g α i j)
      (extChartAt I α).target := chartGramOnE_contDiffOn (I := I) g α i j
  have hG_diff : DifferentiableAt ℝ (chartGramOnE (I := I) g α i j)
      (chartCurve (I := I) α γ t) := by
    have hint : ContDiffOn ℝ ∞ (chartGramOnE (I := I) g α i j)
        (interior (extChartAt I α).target) := hG_cd.mono interior_subset
    have hnhd : interior (extChartAt I α).target ∈
        𝓝 (chartCurve (I := I) α γ t) := isOpen_interior.mem_nhds hmem
    exact (hint.contDiffAt hnhd).differentiableAt (by simp)
  have hchain : HasDerivAt
      (fun s => chartGramOnE (I := I) g α i j (chartCurve (I := I) α γ s))
      (fderiv ℝ (chartGramOnE (I := I) g α i j) (chartCurve (I := I) α γ t)
        (uPrime t)) t :=
    (hG_diff.hasFDerivAt.comp_hasDerivAt t huPrime)
  rw [fderiv_chartGramOnE_eq_sum_partialDeriv (I := I) g α i j] at hchain
  exact hchain

omit [NeZero (Module.finrank ℝ E)] in
theorem chartGramAlongCurve_hasDerivAt
    (g : SmoothRiemannianMetric I M) (α : M) (γ : ℝ → M) (V W : ℝ → E)
    {uPrime Vprime Wprime : ℝ → E} {t : ℝ}
    (huPrime : HasDerivAt (chartCurve (I := I) α γ) (uPrime t) t)
    (hmem : chartCurve (I := I) α γ t ∈ interior (extChartAt I α).target)
    (hV : HasDerivAt V (Vprime t) t) (hW : HasDerivAt W (Wprime t) t) :
    HasDerivAt (fun s => chartGramAlongCurve (I := I) g α γ V W s)
      (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        ((∑ k : Fin (Module.finrank ℝ E),
              chartCoord (E := E) k (uPrime t) *
                partialDeriv (E := E) k (chartGramOnE (I := I) g α i j)
                  (chartCurve (I := I) α γ t)) *
            chartCoord (E := E) i (V t) * chartCoord (E := E) j (W t)
          + chartGramOnE (I := I) g α i j (chartCurve (I := I) α γ t) *
              chartCoord (E := E) i (Vprime t) * chartCoord (E := E) j (W t)
          + chartGramOnE (I := I) g α i j (chartCurve (I := I) α γ t) *
              chartCoord (E := E) i (V t) * chartCoord (E := E) j (Wprime t)))
      t := by
  classical
  have hterm : ∀ i j : Fin (Module.finrank ℝ E),
      HasDerivAt
        (fun s => chartGramOnE (I := I) g α i j (chartCurve (I := I) α γ s) *
          chartCoord (E := E) i (V s) * chartCoord (E := E) j (W s))
        ((∑ k : Fin (Module.finrank ℝ E),
              chartCoord (E := E) k (uPrime t) *
                partialDeriv (E := E) k (chartGramOnE (I := I) g α i j)
                  (chartCurve (I := I) α γ t)) *
            chartCoord (E := E) i (V t) * chartCoord (E := E) j (W t)
          + chartGramOnE (I := I) g α i j (chartCurve (I := I) α γ t) *
              chartCoord (E := E) i (Vprime t) * chartCoord (E := E) j (W t)
          + chartGramOnE (I := I) g α i j (chartCurve (I := I) α γ t) *
              chartCoord (E := E) i (V t) * chartCoord (E := E) j (Wprime t))
        t := by
    intro i j
    have hG := chartGramOnE_comp_chartCurve_hasDerivAt (I := I) g α γ i j huPrime hmem
    have hVi : HasDerivAt (fun s => chartCoord (E := E) i (V s))
        (chartCoord (E := E) i (Vprime t)) t :=
      chartSectionCoord_hasDerivAt (X := V) (Xprime := Vprime) i hV
    have hWj : HasDerivAt (fun s => chartCoord (E := E) j (W s))
        (chartCoord (E := E) j (Wprime t)) t :=
      chartSectionCoord_hasDerivAt (X := W) (Xprime := Wprime) j hW
    have hGV := hG.mul hVi
    have hGVW := hGV.mul hWj
    convert hGVW using 2
    ring
  have hsum : HasDerivAt
      (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        (fun s => chartGramOnE (I := I) g α i j (chartCurve (I := I) α γ s) *
          chartCoord (E := E) i (V s) * chartCoord (E := E) j (W s)))
      (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        ((∑ k : Fin (Module.finrank ℝ E),
              chartCoord (E := E) k (uPrime t) *
                partialDeriv (E := E) k (chartGramOnE (I := I) g α i j)
                  (chartCurve (I := I) α γ t)) *
            chartCoord (E := E) i (V t) * chartCoord (E := E) j (W t)
          + chartGramOnE (I := I) g α i j (chartCurve (I := I) α γ t) *
              chartCoord (E := E) i (Vprime t) * chartCoord (E := E) j (W t)
          + chartGramOnE (I := I) g α i j (chartCurve (I := I) α γ t) *
              chartCoord (E := E) i (V t) * chartCoord (E := E) j (Wprime t)))
      t :=
    HasDerivAt.sum (fun i _ => HasDerivAt.sum (fun j _ => hterm i j))
  have hfun : (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        (fun s => chartGramOnE (I := I) g α i j (chartCurve (I := I) α γ s) *
          chartCoord (E := E) i (V s) * chartCoord (E := E) j (W s)))
      = (fun s => chartGramAlongCurve (I := I) g α γ V W s) := by
    funext s
    rw [chartGramAlongCurve_def]
    rw [Finset.sum_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_apply]
  rw [hfun] at hsum
  exact hsum

omit [NeZero (Module.finrank ℝ E)] in
lemma chartCoord_chartChristoffelContraction
    (g : SmoothRiemannianMetric I M) (α : M) (v w y : E)
    (l : Fin (Module.finrank ℝ E)) :
    chartCoord (E := E) l
        (chartChristoffelContraction (I := I) g α v w y) =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        chartChristoffel (I := I) g α i j l y *
          chartCoord (E := E) i v * chartCoord (E := E) j w := by
  classical
  rw [chartChristoffelContraction_def, chartCoord, map_sum, Finsupp.finset_sum_apply]
  have hbasis : ∀ k : Fin (Module.finrank ℝ E),
      (chartModelBasis E).repr ((chartModelBasis E) k) l = if k = l then 1 else 0 := by
    intro k
    classical
    exact (chartModelBasis E).repr_self_apply k l
  calc
    ∑ k : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr
          ((∑ i, ∑ j, chartChristoffel (I := I) g α i j k y *
            chartCoord (E := E) i v * chartCoord (E := E) j w) •
            chartModelBasis E k)) l
      = ∑ k : Fin (Module.finrank ℝ E),
          (∑ i, ∑ j, chartChristoffel (I := I) g α i j k y *
            chartCoord (E := E) i v * chartCoord (E := E) j w) *
            ((chartModelBasis E).repr (chartModelBasis E k) l) := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
    _ = ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g α i j l y *
            chartCoord (E := E) i v * chartCoord (E := E) j w := by
        rw [Finset.sum_eq_single l]
        · rw [hbasis l]; simp
        · intro k _ hkl; rw [hbasis k, if_neg hkl]; ring
        · intro hl; exact absurd (Finset.mem_univ l) hl

private lemma sum4_swap_outer_inner {ι : Type*} [Fintype ι]
    (f : ι → ι → ι → ι → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d)
      = ∑ d, ∑ b, ∑ c, ∑ a, f a b c d := by
  classical
  have e1 : (∑ a, ∑ b, ∑ c, ∑ d, f a b c d)
      = ∑ a, ∑ b, ∑ d, ∑ c, f a b c d :=
    Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_comm))
  have e2 : (∑ a, ∑ b, ∑ d, ∑ c, f a b c d)
      = ∑ a, ∑ d, ∑ b, ∑ c, f a b c d :=
    Finset.sum_congr rfl (fun a _ => Finset.sum_comm)
  have e3 : (∑ a, ∑ d, ∑ b, ∑ c, f a b c d)
      = ∑ d, ∑ a, ∑ b, ∑ c, f a b c d := Finset.sum_comm
  have e4 : (∑ d, ∑ a, ∑ b, ∑ c, f a b c d)
      = ∑ d, ∑ b, ∑ c, ∑ a, f a b c d := by
    refine Finset.sum_congr rfl (fun d _ => ?_)
    have g1 : (∑ a, ∑ b, ∑ c, f a b c d) = ∑ b, ∑ a, ∑ c, f a b c d := Finset.sum_comm
    have g2 : (∑ b, ∑ a, ∑ c, f a b c d) = ∑ b, ∑ c, ∑ a, f a b c d :=
      Finset.sum_congr rfl (fun b _ => Finset.sum_comm)
    exact g1.trans g2
  exact e1.trans (e2.trans (e3.trans e4))

private lemma sum3_swap_outer_inner {ι : Type*} [Fintype ι]
    (f : ι → ι → ι → ℝ) :
    (∑ a, ∑ b, ∑ c, f a b c) = ∑ c, ∑ b, ∑ a, f a b c := by
  classical
  have e1 : (∑ a, ∑ b, ∑ c, f a b c) = ∑ a, ∑ c, ∑ b, f a b c :=
    Finset.sum_congr rfl (fun a _ => Finset.sum_comm)
  have e2 : (∑ a, ∑ c, ∑ b, f a b c) = ∑ c, ∑ a, ∑ b, f a b c := Finset.sum_comm
  have e3 : (∑ c, ∑ a, ∑ b, f a b c) = ∑ c, ∑ b, ∑ a, f a b c :=
    Finset.sum_congr rfl (fun c _ => Finset.sum_comm)
  exact e1.trans (e2.trans e3)

omit [NeZero (Module.finrank ℝ E)] in
theorem chartGramAlongCurve_hasDerivAt_covariant
    (g : SmoothRiemannianMetric I M) (α : M) (γ : ℝ → M) (V W : ℝ → E)
    {uPrime Vprime Wprime : ℝ → E} {t : ℝ}
    (huPrime : HasDerivAt (chartCurve (I := I) α γ) (uPrime t) t)
    (hmem : chartCurve (I := I) α γ t ∈ interior (extChartAt I α).target)
    (hV : HasDerivAt V (Vprime t) t) (hW : HasDerivAt W (Wprime t) t) :
    HasDerivAt (fun s => chartGramAlongCurve (I := I) g α γ V W s)
      ((∑ l : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          chartGramOnE (I := I) g α l j (chartCurve (I := I) α γ t) *
            chartCoord (E := E) l
              (Vprime t + chartChristoffelContraction (I := I) g α
                (uPrime t) (V t) (chartCurve (I := I) α γ t)) *
            chartCoord (E := E) j (W t))
        + (∑ i : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
          chartGramOnE (I := I) g α i l (chartCurve (I := I) α γ t) *
            chartCoord (E := E) i (V t) *
            chartCoord (E := E) l
              (Wprime t + chartChristoffelContraction (I := I) g α
                (uPrime t) (W t) (chartCurve (I := I) α γ t))))
      t := by
  classical
  have hbase := chartGramAlongCurve_hasDerivAt (I := I) g α γ V W
    huPrime hmem hV hW
  set u := chartCurve (I := I) α γ t with hu_def
  set G : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun i j => chartGramOnE (I := I) g α i j u with hG_def
  set Γ : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Fin (Module.finrank ℝ E) → ℝ :=
    fun i j l => chartChristoffel (I := I) g α i j l u with hΓ_def
  set Vc : Fin (Module.finrank ℝ E) → ℝ := fun i => chartCoord (E := E) i (V t) with hVc
  set Wc : Fin (Module.finrank ℝ E) → ℝ := fun j => chartCoord (E := E) j (W t) with hWc
  set uc : Fin (Module.finrank ℝ E) → ℝ := fun k => chartCoord (E := E) k (uPrime t) with huc
  set Vpc : Fin (Module.finrank ℝ E) → ℝ := fun i => chartCoord (E := E) i (Vprime t) with hVpc
  set Wpc : Fin (Module.finrank ℝ E) → ℝ := fun j => chartCoord (E := E) j (Wprime t) with hWpc
  have hGsymm : ∀ a b : Fin (Module.finrank ℝ E), G a b = G b a := by
    intro a b; simp only [hG_def]; exact chartGramOnE_symm (I := I) g α a b u
  have hmc : ∀ i j k : Fin (Module.finrank ℝ E),
      partialDeriv (E := E) k (chartGramOnE (I := I) g α i j) u =
        (∑ l, Γ k i l * G l j) + (∑ l, Γ k j l * G l i) := by
    intro i j k
    exact DifferentialGeometry.Geometry.chartGramOnE_partialDeriv_eq_christoffel_sum_split
      (I := I) g α i j k hmem
  have hcovV : ∀ l : Fin (Module.finrank ℝ E),
      chartCoord (E := E) l
          (Vprime t + chartChristoffelContraction (I := I) g α (uPrime t) (V t) u)
        = Vpc l + ∑ k, ∑ i, Γ k i l * uc k * Vc i := by
    intro l
    rw [chartCoord, map_add, Finsupp.add_apply, ← chartCoord, ← chartCoord,
      chartCoord_chartChristoffelContraction (I := I) g α (uPrime t) (V t) u]
  have hcovW : ∀ l : Fin (Module.finrank ℝ E),
      chartCoord (E := E) l
          (Wprime t + chartChristoffelContraction (I := I) g α (uPrime t) (W t) u)
        = Wpc l + ∑ k, ∑ j, Γ k j l * uc k * Wc j := by
    intro l
    rw [chartCoord, map_add, Finsupp.add_apply, ← chartCoord, ← chartCoord,
      chartCoord_chartChristoffelContraction (I := I) g α (uPrime t) (W t) u]
  have hval :
      (∑ l, ∑ j, G l j * chartCoord (E := E) l
          (Vprime t + chartChristoffelContraction (I := I) g α (uPrime t) (V t) u) * Wc j)
        + (∑ i, ∑ l, G i l * Vc i *
            chartCoord (E := E) l
              (Wprime t + chartChristoffelContraction (I := I) g α (uPrime t) (W t) u))
      = (∑ i, ∑ j,
          ((∑ k, uc k * partialDeriv (E := E) k (chartGramOnE (I := I) g α i j) u) *
              Vc i * Wc j
            + G i j * Vpc i * Wc j
            + G i j * Vc i * Wpc j)) := by
    rw [show
        (∑ l, ∑ j, G l j * chartCoord (E := E) l
            (Vprime t + chartChristoffelContraction (I := I) g α (uPrime t) (V t) u) * Wc j)
          = ∑ l, ∑ j, G l j * (Vpc l + ∑ k, ∑ i, Γ k i l * uc k * Vc i) * Wc j from
      Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun j _ => by rw [hcovV l]))]
    rw [show
        (∑ i, ∑ l, G i l * Vc i * chartCoord (E := E) l
            (Wprime t + chartChristoffelContraction (I := I) g α (uPrime t) (W t) u))
          = ∑ i, ∑ l, G i l * Vc i * (Wpc l + ∑ k, ∑ j, Γ k j l * uc k * Wc j) from
      Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun l _ => by rw [hcovW l]))]
    rw [show
        (∑ i, ∑ j,
          ((∑ k, uc k * partialDeriv (E := E) k (chartGramOnE (I := I) g α i j) u) *
              Vc i * Wc j + G i j * Vpc i * Wc j + G i j * Vc i * Wpc j))
          = ∑ i, ∑ j,
            ((∑ k, uc k * ((∑ l, Γ k i l * G l j) + (∑ l, Γ k j l * G l i))) *
                Vc i * Wc j + G i j * Vpc i * Wc j + G i j * Vc i * Wpc j) from
      Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by
        simp only [hmc i j]))]
    have hLHS :
        (∑ l, ∑ j, G l j * (Vpc l + ∑ k, ∑ i, Γ k i l * uc k * Vc i) * Wc j)
          + (∑ i, ∑ l, G i l * Vc i * (Wpc l + ∑ k, ∑ j, Γ k j l * uc k * Wc j))
        = (∑ l, ∑ j, G l j * Vpc l * Wc j)
          + (∑ i, ∑ l, G i l * Vc i * Wpc l)
          + (∑ l, ∑ j, ∑ k, ∑ i, G l j * (Γ k i l * uc k * Vc i) * Wc j)
          + (∑ i, ∑ l, ∑ k, ∑ j, G i l * Vc i * (Γ k j l * uc k * Wc j)) := by
      simp only [mul_add, add_mul, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
      ring_nf
    have hRHS :
        (∑ i, ∑ j,
          ((∑ k, uc k * ((∑ l, Γ k i l * G l j) + (∑ l, Γ k j l * G l i))) *
              Vc i * Wc j + G i j * Vpc i * Wc j + G i j * Vc i * Wpc j))
        = (∑ i, ∑ j, G i j * Vpc i * Wc j)
          + (∑ i, ∑ j, G i j * Vc i * Wpc j)
          + (∑ i, ∑ j, ∑ k, ∑ l, uc k * (Γ k i l * G l j) * Vc i * Wc j)
          + (∑ i, ∑ j, ∑ k, ∑ l, uc k * (Γ k j l * G l i) * Vc i * Wc j) := by
      simp only [mul_add, add_mul, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
      ring_nf
    rw [hLHS, hRHS]
    have hCV : (∑ l, ∑ j, ∑ k, ∑ i, G l j * (Γ k i l * uc k * Vc i) * Wc j)
        = ∑ i, ∑ j, ∑ k, ∑ l, uc k * (Γ k i l * G l j) * Vc i * Wc j := by
      rw [sum4_swap_outer_inner (fun l j k i => G l j * (Γ k i l * uc k * Vc i) * Wc j)]
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ =>
        Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => by ring))))
    have hCW : (∑ i, ∑ l, ∑ k, ∑ j, G i l * Vc i * (Γ k j l * uc k * Wc j))
        = ∑ i, ∑ j, ∑ k, ∑ l, uc k * (Γ k j l * G l i) * Vc i * Wc j := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [sum3_swap_outer_inner (fun l k j => G i l * Vc i * (Γ k j l * uc k * Wc j))]
      refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ =>
        Finset.sum_congr rfl (fun l _ => ?_)))
      rw [hGsymm i l]; ring
    rw [hCV, hCW]
  rw [show (∑ l, ∑ j, chartGramOnE (I := I) g α l j u *
        chartCoord (E := E) l
          (Vprime t + chartChristoffelContraction (I := I) g α (uPrime t) (V t) u) *
        chartCoord (E := E) j (W t))
      + (∑ i, ∑ l, chartGramOnE (I := I) g α i l u *
          chartCoord (E := E) i (V t) *
          chartCoord (E := E) l
            (Wprime t + chartChristoffelContraction (I := I) g α (uPrime t) (W t) u))
      = (∑ i, ∑ j,
          ((∑ k, chartCoord (E := E) k (uPrime t) *
                partialDeriv (E := E) k (chartGramOnE (I := I) g α i j) u) *
              chartCoord (E := E) i (V t) * chartCoord (E := E) j (W t)
            + chartGramOnE (I := I) g α i j u *
                chartCoord (E := E) i (Vprime t) * chartCoord (E := E) j (W t)
            + chartGramOnE (I := I) g α i j u *
                chartCoord (E := E) i (V t) * chartCoord (E := E) j (Wprime t))) from hval]
  exact hbase

end MetricCompatibilityAlongCurve

end AlongCurve
end Riemannian
end Geometry
end DifferentialGeometry
