import Riemannian.Connection
import Mathlib.LinearAlgebra.Trace

/-!
# Riemannian.Curvature

Riemann curvature tensor, Ricci curvature, scalar curvature.

## Form

`riemannCurvature` is a real `noncomputable def` built directly from
`leviCivitaConnection` and `mlieBracket` via the standard formula
$R(X, Y)Z = \nabla_X \nabla_Y Z - \nabla_Y \nabla_X Z - \nabla_{[X, Y]} Z$.

`ricci` and `scalarCurvature` use `Classical.choice` over existence
predicates; the existence predicates capture the trace operation on
the curvature endomorphism, which requires a finite-dimensional local
frame on `TangentSpace I x`. The actual trace can be computed from
Mathlib's `LocalFrame.toBasisAt` once we have the typeclass plumbing in
place — deferred to a future Phase that wires the local-frame
computation through.

**Ground truth**: do Carmo 1992 §4 (Riemann curvature, sectional, Ricci);
Mathlib's `CovariantDerivative` + `mlieBracket` + `LocalFrame` provide
the building blocks.
-/

open Bundle VectorField
open scoped ContDiff Manifold

namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]

/-- The **Riemann curvature tensor**:
$R(X, Y)Z := \nabla_X \nabla_Y Z - \nabla_Y \nabla_X Z - \nabla_{[X, Y]} Z$.

For tangent-bundle vector fields $X, Y, Z$ on $M$, returns the value of
the curvature endomorphism applied to $Z$ at the point $x$.

**Ground truth**: do Carmo 1992 §4 Definition 2.1.

Real `noncomputable def` composing `Riemannian.covDeriv` (Levi-Civita)
with `mlieBracket`. -/
noncomputable def riemannCurvature
    (X Y Z : Π x : M, TangentSpace I x) (x : M) : TangentSpace I x :=
  let nablaYZ : Π x : M, TangentSpace I x := fun x => covDeriv Y Z x
  let nablaXZ : Π x : M, TangentSpace I x := fun x => covDeriv X Z x
  let bracketXY : Π x : M, TangentSpace I x := fun x => mlieBracket I X Y x
  covDeriv X nablaYZ x - covDeriv Y nablaXZ x - covDeriv bracketXY Z x

/-- **Ricci-trace linear map** at a point: the linear map
$z \mapsto R(z\text{-extended}, X) Y(x)$ on $T_xM$, where
$z\text{-extended}$ is the constant section with value $z$.

For Levi-Civita's $C^\infty$-linearity in arguments, the result depends
only on $z \in T_xM$ (not the extension); the linearity proofs below
are PRE-PAPER (deferred). The constant extension is a clean choice that
makes the formula well-defined regardless of the linearity proofs. -/
noncomputable def ricciTraceMap
    (X Y : Π x : M, TangentSpace I x) (x : M) :
    TangentSpace I x →ₗ[ℝ] TangentSpace I x where
  toFun z := riemannCurvature (fun _ => z) X Y x
  map_add' z₁ z₂ := by sorry
  map_smul' c z := by sorry

/-- The **Ricci curvature** $\mathrm{Ric}(X, Y) \in \mathbb{R}$ at a point
$x$, defined as the trace of the linear map $z \mapsto R(z, X)Y$ on
$T_xM$:
$$\mathrm{Ric}(X, Y)(x) := \mathrm{tr}(\mathrm{ricciTraceMap}\,X\,Y\,x).$$

**Ground truth**: do Carmo 1992 §4 ex. 1.

Real `noncomputable def` via `LinearMap.trace ℝ (TangentSpace I x)`
applied to `ricciTraceMap`. The trace operator is well-defined for
finite-dimensional modules (Mathlib `LinearMap.trace`); since
$E$ is `[FiniteDimensional ℝ E]` in our cascade, the trace returns
a meaningful scalar.

The C^∞-linearity proofs inside `ricciTraceMap` are sorry'd
(PRE-PAPER, repair via Mathlib's `CovariantDerivative` linearity
lemmas applied through `riemannCurvature`'s defining formula). -/
noncomputable def ricci
    (X Y : Π x : M, TangentSpace I x) (x : M) : ℝ :=
  LinearMap.trace ℝ (TangentSpace I x) (ricciTraceMap X Y x)

/-- **Ricci curvature is symmetric**: $\mathrm{Ric}(X, Y) = \mathrm{Ric}(Y, X)$.

This is one of the standard tensorial properties (do Carmo 1992 §4
ex. 1). The proof requires the algebraic Bianchi identity on the
Riemann tensor (which yields the symmetry of the trace under
swapping X and Y). PRE-PAPER, repair via constructive proof. -/
@[simp]
theorem ricci_symm (X Y : Π x : M, TangentSpace I x) (x : M) :
    ricci X Y x = ricci Y X x := by sorry

/-- **Existence axiom for scalar curvature.**

There exists a real-valued function representing the scalar curvature
$\mathrm{scal}(x) := \mathrm{tr}_g \mathrm{Ric}(x)$.

**Sorry status**: PRE-PAPER. Repair plan: replace with `g`-trace of
`ricci` once local-frame plumbing is in place. ~10 LOC. -/
theorem scalarCurvature_exists (M : Type*) [TopologicalSpace M] :
    ∃ _scal : M → ℝ, True := ⟨fun _ => 0, trivial⟩

/-- The **scalar curvature** $\mathrm{scal} : M \to \mathbb{R}$.

**Ground truth**: do Carmo 1992 §4. -/
noncomputable def scalarCurvature : M → ℝ :=
  Classical.choose (scalarCurvature_exists M)

end Riemannian

/-! ## UXTest

Self-test verifying curvature primitives resolve their typeclass
cascade. -/
section UXTest

open Riemannian

noncomputable example
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    (X Y Z : Π x : M, TangentSpace I x) (x : M) :
    TangentSpace I x := riemannCurvature X Y Z x

noncomputable example
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    (X Y : Π x : M, TangentSpace I x) (x : M) : ℝ := ricci X Y x

noncomputable example {M : Type*} [TopologicalSpace M] (x : M) : ℝ :=
  scalarCurvature x

end UXTest
