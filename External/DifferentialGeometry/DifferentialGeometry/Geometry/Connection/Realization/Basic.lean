import Mathlib.Geometry.Manifold.DerivationBundle
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorField.LieBracket
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.LinearAlgebra.Trace
import Mathlib.Analysis.InnerProductSpace.Dual
import DifferentialGeometry.Bundle.Section
import DifferentialGeometry.Tensor.RSTensor.Defs


noncomputable section

open scoped Manifold ContDiff
open Bundle

section SmoothRicciFlowContext

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

section InstanceVerification

example : CommRing C^∞⟮I, M; ℝ⟯ := inferInstance
example : Algebra ℝ C^∞⟮I, M; ℝ⟯ := inferInstance
example : Module C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ := inferInstance
example : Module ℝ Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ := inferInstance
example (x : M) : Module.Free ℝ (TangentSpace I x) := inferInstance
example (x : M) : FiniteDimensional ℝ (TangentSpace I x) := inferInstance
example : ContMDiffVectorBundle ∞ E (TangentSpace I : M → Type _) I := inferInstance

end InstanceVerification

instance smoothSectionScalarTower :
    IsScalarTower ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ where
  smul_assoc r f s := by ext x; exact mul_smul (r : ℝ) (f x : ℝ) (s x)

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] in
private theorem two_smooth_eval (x : M) : (2 : C^∞⟮I, M; ℝ⟯) x = (2 : ℝ) := by
  have h2a : (2 : C^∞⟮I, M; ℝ⟯) * (1 : C^∞⟮I, M; ℝ⟯) = (2 : C^∞⟮I, M; ℝ⟯) := mul_one _
  have h_two_eq : (2 : C^∞⟮I, M; ℝ⟯) = (1 : C^∞⟮I, M; ℝ⟯) + (1 : C^∞⟮I, M; ℝ⟯) := by norm_num
  have := DFunLike.congr_fun h_two_eq x
  simp only [ContMDiffMap.coe_add, Pi.add_apply, ContMDiffMap.coe_one, Pi.one_apply] at this
  linarith

noncomputable instance invertible2SmoothFunctions :
    Invertible (2 : C^∞⟮I, M; ℝ⟯) where
  invOf := algebraMap ℝ C^∞⟮I, M; ℝ⟯ (1/2 : ℝ)
  invOf_mul_self := by
    apply ContMDiffMap.ext; intro x
    have : (algebraMap ℝ C^∞⟮I, M; ℝ⟯ (1/2 : ℝ) * (2 : C^∞⟮I, M; ℝ⟯)) x =
        (1/2 : ℝ) * (2 : C^∞⟮I, M; ℝ⟯) x := by
      simp only [ContMDiffMap.coe_mul, Pi.mul_apply, Algebra.algebraMap_eq_smul_one,
        ContMDiffMap.coe_smul, Pi.smul_apply, smul_eq_mul, ContMDiffMap.coe_one,
        Pi.one_apply, mul_one]
    rw [this, two_smooth_eval, ContMDiffMap.coe_one, Pi.one_apply]; norm_num
  mul_invOf_self := by
    apply ContMDiffMap.ext; intro x
    have : ((2 : C^∞⟮I, M; ℝ⟯) * algebraMap ℝ C^∞⟮I, M; ℝ⟯ (1/2 : ℝ)) x =
        (2 : C^∞⟮I, M; ℝ⟯) x * (1/2 : ℝ) := by
      simp only [ContMDiffMap.coe_mul, Pi.mul_apply, Algebra.algebraMap_eq_smul_one,
        ContMDiffMap.coe_smul, Pi.smul_apply, smul_eq_mul, ContMDiffMap.coe_one,
        Pi.one_apply, mul_one]
    rw [this, two_smooth_eval, ContMDiffMap.coe_one, Pi.one_apply]; norm_num

end SmoothRicciFlowContext

end
