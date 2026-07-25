import DifferentialGeometry.Geometry.Operator.Gradient
import DifferentialGeometry.Geometry.Operator.Laplacian


noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold Topology ContDiff Matrix

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Forms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Measure

def codifferentialOfVectorField [I.Boundaryless] [T2Space M]
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) : M → ℝ :=
  fun y => -divergence_g (I := I) g X y

omit [InnerProductSpace ℝ E] in
@[simp] lemma codifferentialOfVectorField_def [I.Boundaryless] [T2Space M]
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (y : M) :
    codifferentialOfVectorField (I := I) g X y =
      -divergence_g (I := I) g X y := rfl

omit [InnerProductSpace ℝ E] in
theorem codifferentialOfVectorField_contMDiff [I.Boundaryless] [T2Space M]
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiff I 𝓘(ℝ) ∞ (codifferentialOfVectorField (I := I) g X) := by
  have hdiv : ContMDiff I 𝓘(ℝ) ∞ (divergence_g (I := I) g X) :=
    divergence_g_contMDiff (I := I) g X
  have hneg : ContMDiff I 𝓘(ℝ) ∞ (fun y : M => -divergence_g (I := I) g X y) :=
    hdiv.neg
  exact hneg

omit [InnerProductSpace ℝ E] in
theorem codifferentialOfVectorField_add [I.Boundaryless] [T2Space M]
    (g : SmoothRiemannianMetric I M)
    (X Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (y : M) :
    codifferentialOfVectorField (I := I) g (X + Y) y =
      codifferentialOfVectorField (I := I) g X y +
        codifferentialOfVectorField (I := I) g Y y := by
  change -divergence_g (I := I) g (X + Y) y =
    -divergence_g (I := I) g X y + -divergence_g (I := I) g Y y
  rw [divergence_g_add (I := I) g X Y y]
  ring

omit [InnerProductSpace ℝ E] in
@[simp] theorem codifferentialOfVectorField_zero [I.Boundaryless] [T2Space M]
    (g : SmoothRiemannianMetric I M) (y : M) :
    codifferentialOfVectorField (I := I) g
        (0 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) y = 0 := by
  change -divergence_g (I := I) g
      (0 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) y = 0
  rw [divergence_g_zero (I := I) g y]
  exact neg_zero

def formLaplacianScalar [I.Boundaryless] [T2Space M]
    (g : SmoothRiemannianMetric I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) : M → ℝ :=
  codifferentialOfVectorField (I := I) g (grad_g (I := I) g hf)

omit [InnerProductSpace ℝ E] in
@[simp] lemma formLaplacianScalar_def [I.Boundaryless] [T2Space M]
    (g : SmoothRiemannianMetric I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (y : M) :
    formLaplacianScalar (I := I) g hf y =
      codifferentialOfVectorField (I := I) g (grad_g (I := I) g hf) y := rfl

omit [InnerProductSpace ℝ E] in
theorem formLaplacianScalar_eq_neg_Δ_g [I.Boundaryless] [T2Space M]
    (g : SmoothRiemannianMetric I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (y : M) :
    formLaplacianScalar (I := I) g hf y =
      -DifferentialGeometry.Integral.DivergenceTheorem.Δ_g (I := I) g hf y := by
  change codifferentialOfVectorField (I := I) g (grad_g (I := I) g hf) y =
    -DifferentialGeometry.Integral.DivergenceTheorem.Δ_g (I := I) g hf y
  rw [codifferentialOfVectorField_def (I := I) g (grad_g (I := I) g hf) y]
  rw [DifferentialGeometry.Integral.DivergenceTheorem.Δ_g_def (I := I) g hf y]

omit [InnerProductSpace ℝ E] in
theorem formLaplacianScalar_contMDiff [I.Boundaryless] [T2Space M]
    (g : SmoothRiemannianMetric I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    ContMDiff I 𝓘(ℝ) ∞ (formLaplacianScalar (I := I) g hf) :=
  codifferentialOfVectorField_contMDiff (I := I) g (grad_g (I := I) g hf)

omit [InnerProductSpace ℝ E] in
@[simp] theorem formLaplacianScalar_zero [I.Boundaryless] [T2Space M]
    (g : SmoothRiemannianMetric I M)
    (h0 : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun _ : M => (0 : ℝ))) (y : M) :
    formLaplacianScalar (I := I) g h0 y = 0 := by
  rw [formLaplacianScalar_eq_neg_Δ_g (I := I) g h0 y]
  have hgrad_zero : (grad_g (I := I) g h0 :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) =
      (0 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) := by
    apply ContMDiffSection.ext
    intro x
    change gradFun (I := I) g (fun _ : M => (0 : ℝ)) x =
        (0 : TangentSpace I x)
    apply gradFun_eq_zero_of_mfderiv_eq_zero
    exact mfderiv_const
  change -DifferentialGeometry.Integral.DivergenceTheorem.Δ_g (I := I) g h0 y = 0
  rw [DifferentialGeometry.Integral.DivergenceTheorem.Δ_g_def (I := I) g h0 y]
  rw [hgrad_zero]
  rw [divergence_g_zero (I := I) g y]
  exact neg_zero

omit [InnerProductSpace ℝ E] in
theorem formLaplacianScalar_add [I.Boundaryless] [T2Space M]
    (g : SmoothRiemannianMetric I M)
    {f h : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hh : ContMDiff I 𝓘(ℝ, ℝ) ∞ h)
    (hfh : ContMDiff I 𝓘(ℝ, ℝ) ∞ (f + h)) (y : M) :
    formLaplacianScalar (I := I) g hfh y =
      formLaplacianScalar (I := I) g hf y +
        formLaplacianScalar (I := I) g hh y := by
  rw [formLaplacianScalar_eq_neg_Δ_g (I := I) g hfh y]
  rw [formLaplacianScalar_eq_neg_Δ_g (I := I) g hf y]
  rw [formLaplacianScalar_eq_neg_Δ_g (I := I) g hh y]
  have hgrad_sum :
      (grad_g (I := I) g hfh : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) =
        (grad_g (I := I) g hf :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) +
        (grad_g (I := I) g hh :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) := by
    apply ContMDiffSection.ext
    intro x
    change gradFun (I := I) g (f + h) x =
      gradFun (I := I) g f x + gradFun (I := I) g h x
    exact gradFun_add (I := I) g
      (hf.mdifferentiable (by simp) x) (hh.mdifferentiable (by simp) x)
  change -DifferentialGeometry.Integral.DivergenceTheorem.Δ_g (I := I) g hfh y =
    -DifferentialGeometry.Integral.DivergenceTheorem.Δ_g (I := I) g hf y +
      -DifferentialGeometry.Integral.DivergenceTheorem.Δ_g (I := I) g hh y
  rw [DifferentialGeometry.Integral.DivergenceTheorem.Δ_g_def (I := I) g hfh y]
  rw [DifferentialGeometry.Integral.DivergenceTheorem.Δ_g_def (I := I) g hf y]
  rw [DifferentialGeometry.Integral.DivergenceTheorem.Δ_g_def (I := I) g hh y]
  rw [hgrad_sum]
  rw [divergence_g_add (I := I) g
        (grad_g (I := I) g hf) (grad_g (I := I) g hh) y]
  ring

end Forms
end Riemannian
end Geometry
end DifferentialGeometry
