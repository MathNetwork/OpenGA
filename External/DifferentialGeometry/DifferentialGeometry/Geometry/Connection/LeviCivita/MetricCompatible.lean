import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import DifferentialGeometry.Analysis.Integration.Measure.ChartDensity


noncomputable section

open Bundle Manifold Set
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Integral
namespace Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def IsMetricCompatibleOn
    (cov : (Π x : M, TangentSpace I x) →
      (Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x))
    (g : Measure.SmoothRiemannianMetric I M) (s : Set M := Set.univ) : Prop :=
  ∀ ⦃Y Z : Π x : M, TangentSpace I x⦄ ⦃x : M⦄,
    MDiffAt (T% Y) x → MDiffAt (T% Z) x → x ∈ s →
    ∀ v : TangentSpace I x,
      (mfderiv I 𝓘(ℝ) (fun b => g.inner b (Y b) (Z b)) x) v =
        g.inner x (cov Y x v) (Z x) + g.inner x (Y x) (cov Z x v)

def IsMetricCompatible (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (g : Measure.SmoothRiemannianMetric I M) : Prop :=
  IsMetricCompatibleOn cov.toFun g Set.univ

def metricCompatibleDifferential
    (g : Measure.SmoothRiemannianMetric I M) {x : M}
    (covY : TangentSpace I x →L[ℝ] TangentSpace I x)
    (covZ : TangentSpace I x →L[ℝ] TangentSpace I x)
    (Yx Zx : TangentSpace I x) : TangentSpace I x →L[ℝ] ℝ :=
  (g.inner x Zx).comp covY + (g.inner x Yx).comp covZ

omit [FiniteDimensional ℝ E] in
@[simp]
lemma metricCompatibleDifferential_apply
    (g : Measure.SmoothRiemannianMetric I M) {x : M}
    (covY : TangentSpace I x →L[ℝ] TangentSpace I x)
    (covZ : TangentSpace I x →L[ℝ] TangentSpace I x)
    (Yx Zx : TangentSpace I x) (v : TangentSpace I x) :
    metricCompatibleDifferential g covY covZ Yx Zx v =
      g.inner x Zx (covY v) + g.inner x Yx (covZ v) := rfl

namespace IsMetricCompatibleOn

variable
    {cov : (Π x : M, TangentSpace I x) →
      (Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x)}
    {g : Measure.SmoothRiemannianMetric I M}

omit [FiniteDimensional ℝ E] in
lemma mono {s t : Set M} (h : IsMetricCompatibleOn cov g t) (hst : s ⊆ t) :
    IsMetricCompatibleOn cov g s :=
  fun _Y _Z _x hY hZ hxs v => h hY hZ (hst hxs) v

omit [FiniteDimensional ℝ E] in
lemma iUnion {ι : Type*} {s : ι → Set M}
    (h : ∀ i, IsMetricCompatibleOn cov g (s i)) :
    IsMetricCompatibleOn cov g (⋃ i, s i) := by
  intro Y Z x hY hZ hx v
  obtain ⟨si, ⟨i, rfl⟩, hxsi⟩ := hx
  exact h i hY hZ hxsi v

omit [FiniteDimensional ℝ E] in
lemma swap {s : Set M} (h : IsMetricCompatibleOn cov g s)
    {Y Z : Π x : M, TangentSpace I x} {x : M}
    (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) (hxs : x ∈ s)
    (v : TangentSpace I x) :
    (mfderiv I 𝓘(ℝ) (fun b => g.inner b (Z b) (Y b)) x) v =
      g.inner x (cov Z x v) (Y x) + g.inner x (Z x) (cov Y x v) := by
  have hfun : (fun b => g.inner b (Z b) (Y b)) = (fun b => g.inner b (Y b) (Z b)) := by
    funext b; exact (g.symm b (Z b) (Y b))
  rw [hfun]
  have hYZ := h hY hZ hxs v
  rw [g.symm x (cov Z x v) (Y x), g.symm x (Z x) (cov Y x v),
      add_comm]
  exact hYZ

omit [FiniteDimensional ℝ E] in
lemma apply {s : Set M} (h : IsMetricCompatibleOn cov g s)
    {Y Z : Π x : M, TangentSpace I x} {x : M}
    (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) (hxs : x ∈ s)
    (v : TangentSpace I x) :
    (mfderiv I 𝓘(ℝ) (fun b => g.inner b (Y b) (Z b)) x) v =
      g.inner x (cov Y x v) (Z x) + g.inner x (Y x) (cov Z x v) :=
  h hY hZ hxs v

omit [FiniteDimensional ℝ E] in
lemma hasMFDerivAt {s : Set M} (h : IsMetricCompatibleOn cov g s)
    {Y Z : Π x : M, TangentSpace I x} {x : M}
    (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) (hxs : x ∈ s)
    (hsmooth : MDifferentiableAt I 𝓘(ℝ) (fun b => g.inner b (Y b) (Z b)) x) :
    HasMFDerivAt I 𝓘(ℝ) (fun b => g.inner b (Y b) (Z b)) x
      (metricCompatibleDifferential g (cov Y x) (cov Z x) (Y x) (Z x)) := by
  refine hsmooth.hasMFDerivAt.congr_mfderiv ?_
  ext v
  change (mfderiv I 𝓘(ℝ) (fun b => g.inner b (Y b) (Z b)) x) v =
      g.inner x (Z x) (cov Y x v) + g.inner x (Y x) (cov Z x v)
  rw [h hY hZ hxs v, g.symm x (cov Y x v) (Z x)]

end IsMetricCompatibleOn

namespace IsMetricCompatible

variable {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
variable {g : Measure.SmoothRiemannianMetric I M}

omit [FiniteDimensional ℝ E] in
lemma apply (h : IsMetricCompatible cov g)
    {Y Z : Π x : M, TangentSpace I x} {x : M}
    (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x)
    (v : TangentSpace I x) :
    (mfderiv I 𝓘(ℝ) (fun b => g.inner b (Y b) (Z b)) x) v =
      g.inner x (cov.toFun Y x v) (Z x) + g.inner x (Y x) (cov.toFun Z x v) :=
  h hY hZ (Set.mem_univ _) v

omit [FiniteDimensional ℝ E] in
lemma swap (h : IsMetricCompatible cov g)
    {Y Z : Π x : M, TangentSpace I x} {x : M}
    (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x)
    (v : TangentSpace I x) :
    (mfderiv I 𝓘(ℝ) (fun b => g.inner b (Z b) (Y b)) x) v =
      g.inner x (cov.toFun Z x v) (Y x) + g.inner x (Z x) (cov.toFun Y x v) :=
  IsMetricCompatibleOn.swap h hY hZ (Set.mem_univ _) v

omit [FiniteDimensional ℝ E] in
lemma hasMFDerivAt (h : IsMetricCompatible cov g)
    {Y Z : Π x : M, TangentSpace I x} {x : M}
    (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x)
    (hsmooth :
      MDifferentiableAt I 𝓘(ℝ) (fun b => g.inner b (Y b) (Z b)) x) :
    HasMFDerivAt I 𝓘(ℝ) (fun b => g.inner b (Y b) (Z b)) x
      (metricCompatibleDifferential g (cov.toFun Y x) (cov.toFun Z x) (Y x) (Z x)) :=
  IsMetricCompatibleOn.hasMFDerivAt h hY hZ (Set.mem_univ _) hsmooth

omit [FiniteDimensional ℝ E] in
lemma toIsMetricCompatibleOn (h : IsMetricCompatible cov g) {s : Set M} :
    IsMetricCompatibleOn cov.toFun g s :=
  IsMetricCompatibleOn.mono (t := Set.univ) h (fun _ _ => trivial)

omit [FiniteDimensional ℝ E] in
@[simp]
lemma toIsMetricCompatibleOn_univ_iff :
    IsMetricCompatibleOn cov.toFun g Set.univ ↔ IsMetricCompatible cov g := Iff.rfl

end IsMetricCompatible

omit [FiniteDimensional ℝ E] in
lemma IsMetricCompatibleOn.toIsMetricCompatible
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    {g : Measure.SmoothRiemannianMetric I M}
    (h : IsMetricCompatibleOn cov.toFun g Set.univ) :
    IsMetricCompatible cov g := h

end Connection
end Integral
end DifferentialGeometry
