import DifferentialGeometry.Geometry.Operator.Hessian
import DifferentialGeometry.Geometry.Curvature.Riemann.Defs
import DifferentialGeometry.Geometry.Metric.TensorInner.TangentRiemannian
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian


noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold Topology ContDiff Matrix

namespace DifferentialGeometry
namespace Integral
namespace DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure

def normGradSqFun (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M) : ℝ :=
  g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g f x)

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma normGradSqFun_def
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M) :
    normGradSqFun (I := I) g f x =
      g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g f x) := rfl

omit [NeZero (Module.finrank ℝ E)] in
lemma normGradSqFun_nonneg
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M) :
    0 ≤ normGradSqFun (I := I) g f x := by
  classical
  by_cases hgf : gradFun (I := I) g f x = 0
  · change 0 ≤ g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g f x)
    rw [hgf]
    have hmap : g.inner x (0 : TangentSpace I x) = (0 : TangentSpace I x →L[ℝ] ℝ) :=
      map_zero _
    rw [hmap]
    exact le_refl _
  · change 0 ≤ g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g f x)
    exact le_of_lt (g.pos x _ hgf)

namespace BochnerInternal

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma contMDiff_g_inner_aux
    (g : SmoothRiemannianMetric I M)
    {v w : ∀ x : M, TangentSpace I x}
    (hv : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E
        (E := (TangentSpace I : M → Type _)) x (v x)))
    (hw : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E
        (E := (TangentSpace I : M → Type _)) x (w x))) :
    ContMDiff I 𝓘(ℝ) ∞ (fun b : M => g.inner b (v b) (w b)) := by
  letI rb : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have h := ContMDiff.inner_bundle (F := E) (B := M) (E := (TangentSpace I : M → Type _))
    (b := fun x => x) (v := v) (w := w) hv hw
  refine h.congr ?_
  intro b
  rfl

end BochnerInternal

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem contMDiff_g_inner_of_smooth_sections
    (g : SmoothRiemannianMetric I M)
    (X Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiff I 𝓘(ℝ) ∞ (fun b : M => g.inner b (X b) (Y b)) := by
  have hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E
        (E := (TangentSpace I : M → Type _)) x (X x)) := X.contMDiff
  have hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E
        (E := (TangentSpace I : M → Type _)) x (Y x)) := Y.contMDiff
  exact BochnerInternal.contMDiff_g_inner_aux (I := I) (M := M) g hX hY

omit [NeZero (Module.finrank ℝ E)] in
theorem normGradSqFun_continuous [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    Continuous (normGradSqFun (I := I) g f) := by
  have h :=
    TangentBundle.continuous_g_inner_of_smooth_sections (I := I) (M := M) g
      (grad_g (I := I) g hf) (grad_g (I := I) g hf)
  refine h.congr ?_
  intro b
  change g.inner b ((grad_g (I := I) g hf :
      Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) b)
        ((grad_g (I := I) g hf :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) b) =
      normGradSqFun (I := I) g f b
  rw [grad_g_apply]
  rfl

omit [NeZero (Module.finrank ℝ E)] in
theorem normGradSqFun_contMDiff [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    ContMDiff I 𝓘(ℝ) ∞ (normGradSqFun (I := I) g f) := by
  have h :=
    contMDiff_g_inner_of_smooth_sections (I := I) (M := M) g
      (grad_g (I := I) g hf) (grad_g (I := I) g hf)
  refine h.congr ?_
  intro b
  change g.inner b ((grad_g (I := I) g hf :
      Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) b)
        ((grad_g (I := I) g hf :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) b) =
      normGradSqFun (I := I) g f b
  rw [grad_g_apply]
  rfl

end DivergenceTheorem
end Integral
end DifferentialGeometry
