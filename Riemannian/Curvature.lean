import Riemannian.Connection
import Riemannian.InnerProductBridge
import Mathlib.LinearAlgebra.Trace
import Mathlib.Analysis.InnerProductSpace.PiL2

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

/-- The **scalar curvature** $\mathrm{scal}(x) := \mathrm{tr}_g \mathrm{Ric}(x)$.

Real `noncomputable def` via summing $\mathrm{Ric}(e_i, e_i)$ over a
standard orthonormal basis $\{e_i\}$ of `TangentSpace I x` (provided
by Mathlib's `stdOrthonormalBasis ℝ (TangentSpace I x)` — applicable
because `Riemannian.InnerProductBridge` gives `InnerProductSpace ℝ`
+ `FiniteDimensional ℝ` on the tangent space).

The choice of orthonormal basis is irrelevant — for any orthonormal
basis the sum equals the metric trace of Ric, which is basis-independent.

**Ground truth**: do Carmo 1992 §4. -/
noncomputable def scalarCurvature (x : M) : ℝ :=
  let e : OrthonormalBasis _ ℝ (TangentSpace I x) :=
    stdOrthonormalBasis ℝ (TangentSpace I x)
  ∑ i, ricci (I := I) (M := M)
    (fun (_ : M) => (e i : TangentSpace I x))
    (fun (_ : M) => (e i : TangentSpace I x)) x

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

noncomputable example
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    (x : M) : ℝ :=
  scalarCurvature (I := I) x

end UXTest
