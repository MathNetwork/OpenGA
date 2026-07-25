import DifferentialGeometry.Geometry.Connection.Realization.Embedding
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion


noncomputable section

set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Topology
open Bundle CovariantDerivative

section Connection

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

noncomputable def concreteConn
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞]
    (X Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ where
  toFun x := cov Y x (X x)
  contMDiff_toFun := by

    have hY_plus : ContMDiff I (I.prod 𝓘(ℝ, E)) (∞ + 1) (T% fun x => Y x) := by
      rw [show (∞ : WithTop ℕ∞) + 1 = ∞ from by simp]
      exact Y.contMDiff
    have hcov_smooth := (‹ContMDiffCovariantDerivative cov ∞›).contMDiff.contMDiff
      (hY_plus.contMDiffOn)

    have hcov_global : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
        (fun x => TotalSpace.mk' (E →L[ℝ] E)
          (E := fun (x : M) => TangentSpace I x →L[ℝ] TangentSpace I x) x (cov Y x)) := by
      rwa [← contMDiffOn_univ]

    have hX_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun x => TotalSpace.mk' E (E := TangentSpace I) x (X x)) :=
      X.contMDiff

    exact ContMDiff.clm_bundle_apply (b := id) hcov_global hX_smooth

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
@[simp]
theorem concreteConn_apply
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞]
    (X Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    concreteConn I M cov X Y x = cov Y x (X x) := by
  rfl

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem concreteConn_add_right
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞]
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    concreteConn I M cov X (Y + Z) = concreteConn I M cov X Y + concreteConn I M cov X Z := by
  apply ContMDiffSection.ext; intro x
  change cov (fun x => Y x + Z x) x (X x) =
    cov Y x (X x) + cov Z x (X x)
  have hY : MDiffAt (T% fun x => Y x) x := Y.mdifferentiableAt
  have hZ : MDiffAt (T% fun x => Z x) x := Z.mdifferentiableAt
  rw [show (fun x => Y x + Z x) = ((fun x => Y x) + fun x => Z x) from rfl,
    cov.isCovariantDerivativeOn.add hY hZ]
  simp [ContinuousLinearMap.add_apply]

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem concreteConn_add_left
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞]
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    concreteConn I M cov (X + Y) Z = concreteConn I M cov X Z + concreteConn I M cov Y Z := by
  apply ContMDiffSection.ext; intro x
  change cov Z x (X x + Y x) = cov Z x (X x) + cov Z x (Y x)
  exact ContinuousLinearMap.map_add (cov Z x) (X x) (Y x)

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem concreteConn_smul_left
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞]
    (f : C^∞⟮I, M; ℝ⟯)
    (X Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    concreteConn I M cov (f • X) Z = f • concreteConn I M cov X Z := by
  apply ContMDiffSection.ext; intro x
  change cov Z x (f x • X x) = f x • cov Z x (X x)
  exact ContinuousLinearMap.map_smul (cov Z x) (f x) (X x)

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem concreteConn_leibniz
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞]
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (f : C^∞⟮I, M; ℝ⟯)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    concreteConn I M cov X (f • Y) =
      vectorFieldActionSmooth I M X f • Y + f • concreteConn I M cov X Y := by
  apply ContMDiffSection.ext; intro x

  change cov (fun x => (f : M → ℝ) x • Y x) x (X x) =
    (vectorFieldActionSmooth I M X f) x • Y x + f x • cov Y x (X x)

  have hY : MDiffAt (T% fun x => Y x) x := Y.mdifferentiableAt
  have hf : MDiffAt (f : M → ℝ) x :=
    f.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hfY_eq : (fun x => (f : M → ℝ) x • Y x) = ((f : M → ℝ) • fun x => Y x) := rfl
  rw [hfY_eq, cov.isCovariantDerivativeOn.leibniz hY hf]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply]

  simp only [vectorFieldActionSmooth, ContMDiffMap.coeFn_mk, vectorFieldAction]
  abel
end Connection

end
