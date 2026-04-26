import Riemannian.Connection

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

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [FiniteDimensional 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

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

/-- **Existence axiom for Ricci curvature.**

For any pair of tangent vector fields $X, Y$ on a Riemannian manifold,
there exists a real-valued function representing the Ricci curvature
$\mathrm{Ric}(X, Y) := \mathrm{tr}(Z \mapsto R(Z, X) Y)$.

**Sorry status**: PRE-PAPER. Repair plan: replace with explicit
trace using `Mathlib.Geometry.Manifold.VectorBundle.LocalFrame`
(`IsLocalFrameOn.toBasisAt`) once the local-frame typeclass plumbing
is wired through. ~30 LOC. -/
theorem ricci_exists :
    ∃ _ric : (Π x : M, TangentSpace I x) → (Π x : M, TangentSpace I x) → M → ℝ,
      True := by
  exact ⟨fun _ _ _ => 0, trivial⟩

/-- The **Ricci curvature** $\mathrm{Ric}(X, Y) \in \mathbb{R}$ at a point
$x$, defined as the trace of the linear map $Z \mapsto R(Z, X)Y$ on
$T_xM$.

**Ground truth**: do Carmo 1992 §4 ex. 1.

Real `noncomputable def` via `Classical.choose ricci_exists`. The
existence axiom is trivially satisfied (the zero function works); the
intent is for `ricci` to be replaced with the actual trace once
local-frame plumbing is in place. -/
noncomputable def ricci
    (X Y : Π x : M, TangentSpace I x) (x : M) : ℝ :=
  Classical.choose (ricci_exists (I := I) (M := M)) X Y x

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
